%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QVNzs7iHNc

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:59 EST 2020

% Result     : Timeout 58.94s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  103 ( 479 expanded)
%              Number of leaves         :   23 ( 133 expanded)
%              Depth                    :   22
%              Number of atoms          : 1198 (7061 expanded)
%              Number of equality atoms :   67 ( 391 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf('0',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18
        = ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X15 ) @ ( sk_C @ X18 @ X15 ) ) @ X15 )
      | ( r2_hidden @ ( sk_C @ X18 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k2_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k2_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X24: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ ( k2_relat_1 @ X0 ) )
        | ( sk_B
          = ( k2_relat_1 @ X0 ) )
        | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ sk_B @ X0 ) ) @ ( sk_C @ sk_B @ X0 ) ) @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X15: $i,X18: $i,X19: $i] :
      ( ( X18
        = ( k2_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_C @ X18 @ X15 ) ) @ X15 )
      | ~ ( r2_hidden @ ( sk_C @ X18 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('13',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('16',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X17 @ X15 ) @ X17 ) @ X15 )
      | ( X16
       != ( k2_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('18',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X17 @ X15 ) @ X17 ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k2_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) @ ( sk_C @ sk_B @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18
        = ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X15 ) @ ( sk_C @ X18 @ X15 ) ) @ X15 )
      | ( r2_hidden @ ( sk_C @ X18 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_D @ X0 @ sk_C_1 ) @ ( sk_C @ X0 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ sk_C_1 ) @ ( sk_C @ X0 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) @ ( sk_C @ sk_B @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('30',plain,(
    ! [X15: $i,X18: $i,X19: $i] :
      ( ( X18
        = ( k2_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_C @ X18 @ X15 ) ) @ X15 )
      | ~ ( r2_hidden @ ( sk_C @ X18 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('31',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('36',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','40'])).

thf('42',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X23: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_D_2 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_1 )
   <= ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ sk_B )
    | ~ ! [X23: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_1 )
    | ~ ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('52',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X17 @ X15 ) @ X17 ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k2_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_1 ) @ X0 ) @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_1 )
   <= ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('58',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ! [X23: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_D_2 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k2_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('61',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X17 @ X15 ) @ X17 ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k2_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('63',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('65',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('67',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ( r2_hidden @ sk_D_2 @ sk_B )
      & ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ sk_B )
    | ~ ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('73',plain,(
    ! [X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['44','49','58','70','71','72'])).

thf('74',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['42','73'])).

thf('75',plain,
    ( ( sk_B != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(demod,[status(thm)],['1','4','74'])).

thf('76',plain,
    ( $false
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['44','49','58','72','70','71'])).

thf('78',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QVNzs7iHNc
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 58.94/59.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 58.94/59.19  % Solved by: fo/fo7.sh
% 58.94/59.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 58.94/59.19  % done 8638 iterations in 58.732s
% 58.94/59.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 58.94/59.19  % SZS output start Refutation
% 58.94/59.19  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 58.94/59.19  thf(sk_A_type, type, sk_A: $i).
% 58.94/59.19  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 58.94/59.19  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 58.94/59.19  thf(sk_E_type, type, sk_E: $i > $i).
% 58.94/59.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 58.94/59.19  thf(sk_B_type, type, sk_B: $i).
% 58.94/59.19  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 58.94/59.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 58.94/59.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 58.94/59.19  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 58.94/59.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 58.94/59.19  thf(sk_D_2_type, type, sk_D_2: $i).
% 58.94/59.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 58.94/59.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 58.94/59.19  thf(sk_C_1_type, type, sk_C_1: $i).
% 58.94/59.19  thf(t23_relset_1, conjecture,
% 58.94/59.19    (![A:$i,B:$i,C:$i]:
% 58.94/59.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 58.94/59.19       ( ( ![D:$i]:
% 58.94/59.19           ( ~( ( r2_hidden @ D @ B ) & 
% 58.94/59.19                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 58.94/59.19         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 58.94/59.19  thf(zf_stmt_0, negated_conjecture,
% 58.94/59.19    (~( ![A:$i,B:$i,C:$i]:
% 58.94/59.19        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 58.94/59.19          ( ( ![D:$i]:
% 58.94/59.19              ( ~( ( r2_hidden @ D @ B ) & 
% 58.94/59.19                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 58.94/59.19            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 58.94/59.19    inference('cnf.neg', [status(esa)], [t23_relset_1])).
% 58.94/59.19  thf('0', plain,
% 58.94/59.19      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 58.94/59.19        | (r2_hidden @ sk_D_2 @ sk_B))),
% 58.94/59.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.94/59.19  thf('1', plain,
% 58.94/59.19      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B)))
% 58.94/59.19         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 58.94/59.19      inference('split', [status(esa)], ['0'])).
% 58.94/59.19  thf('2', plain,
% 58.94/59.19      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.94/59.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.94/59.19  thf(redefinition_k2_relset_1, axiom,
% 58.94/59.19    (![A:$i,B:$i,C:$i]:
% 58.94/59.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 58.94/59.19       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 58.94/59.19  thf('3', plain,
% 58.94/59.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 58.94/59.19         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 58.94/59.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 58.94/59.19      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 58.94/59.19  thf('4', plain,
% 58.94/59.19      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 58.94/59.19      inference('sup-', [status(thm)], ['2', '3'])).
% 58.94/59.19  thf(d5_relat_1, axiom,
% 58.94/59.19    (![A:$i,B:$i]:
% 58.94/59.19     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 58.94/59.19       ( ![C:$i]:
% 58.94/59.19         ( ( r2_hidden @ C @ B ) <=>
% 58.94/59.19           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 58.94/59.19  thf('5', plain,
% 58.94/59.19      (![X15 : $i, X18 : $i]:
% 58.94/59.19         (((X18) = (k2_relat_1 @ X15))
% 58.94/59.19          | (r2_hidden @ 
% 58.94/59.19             (k4_tarski @ (sk_D @ X18 @ X15) @ (sk_C @ X18 @ X15)) @ X15)
% 58.94/59.19          | (r2_hidden @ (sk_C @ X18 @ X15) @ X18))),
% 58.94/59.19      inference('cnf', [status(esa)], [d5_relat_1])).
% 58.94/59.19  thf('6', plain,
% 58.94/59.19      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 58.94/59.19         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 58.94/59.19          | (r2_hidden @ X14 @ X16)
% 58.94/59.19          | ((X16) != (k2_relat_1 @ X15)))),
% 58.94/59.19      inference('cnf', [status(esa)], [d5_relat_1])).
% 58.94/59.19  thf('7', plain,
% 58.94/59.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 58.94/59.19         ((r2_hidden @ X14 @ (k2_relat_1 @ X15))
% 58.94/59.19          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15))),
% 58.94/59.19      inference('simplify', [status(thm)], ['6'])).
% 58.94/59.19  thf('8', plain,
% 58.94/59.19      (![X0 : $i, X1 : $i]:
% 58.94/59.19         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 58.94/59.19          | ((X1) = (k2_relat_1 @ X0))
% 58.94/59.19          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 58.94/59.19      inference('sup-', [status(thm)], ['5', '7'])).
% 58.94/59.19  thf('9', plain,
% 58.94/59.19      (![X24 : $i]:
% 58.94/59.19         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))
% 58.94/59.19          | (r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19          | ~ (r2_hidden @ X24 @ sk_B))),
% 58.94/59.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.94/59.19  thf('10', plain,
% 58.94/59.19      ((![X24 : $i]:
% 58.94/59.19          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19           | ~ (r2_hidden @ X24 @ sk_B)))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('split', [status(esa)], ['9'])).
% 58.94/59.19  thf('11', plain,
% 58.94/59.19      ((![X0 : $i]:
% 58.94/59.19          ((r2_hidden @ (sk_C @ sk_B @ X0) @ (k2_relat_1 @ X0))
% 58.94/59.19           | ((sk_B) = (k2_relat_1 @ X0))
% 58.94/59.19           | (r2_hidden @ 
% 58.94/59.19              (k4_tarski @ (sk_E @ (sk_C @ sk_B @ X0)) @ (sk_C @ sk_B @ X0)) @ 
% 58.94/59.19              sk_C_1)))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['8', '10'])).
% 58.94/59.19  thf('12', plain,
% 58.94/59.19      (![X15 : $i, X18 : $i, X19 : $i]:
% 58.94/59.19         (((X18) = (k2_relat_1 @ X15))
% 58.94/59.19          | ~ (r2_hidden @ (k4_tarski @ X19 @ (sk_C @ X18 @ X15)) @ X15)
% 58.94/59.19          | ~ (r2_hidden @ (sk_C @ X18 @ X15) @ X18))),
% 58.94/59.19      inference('cnf', [status(esa)], [d5_relat_1])).
% 58.94/59.19  thf('13', plain,
% 58.94/59.19      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 58.94/59.19         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['11', '12'])).
% 58.94/59.19  thf('14', plain,
% 58.94/59.19      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 58.94/59.19         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('simplify', [status(thm)], ['13'])).
% 58.94/59.19  thf('15', plain,
% 58.94/59.19      (![X0 : $i, X1 : $i]:
% 58.94/59.19         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 58.94/59.19          | ((X1) = (k2_relat_1 @ X0))
% 58.94/59.19          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 58.94/59.19      inference('sup-', [status(thm)], ['5', '7'])).
% 58.94/59.19  thf('16', plain,
% 58.94/59.19      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k2_relat_1 @ sk_C_1))))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('clc', [status(thm)], ['14', '15'])).
% 58.94/59.19  thf('17', plain,
% 58.94/59.19      (![X15 : $i, X16 : $i, X17 : $i]:
% 58.94/59.19         (~ (r2_hidden @ X17 @ X16)
% 58.94/59.19          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X17 @ X15) @ X17) @ X15)
% 58.94/59.19          | ((X16) != (k2_relat_1 @ X15)))),
% 58.94/59.19      inference('cnf', [status(esa)], [d5_relat_1])).
% 58.94/59.19  thf('18', plain,
% 58.94/59.19      (![X15 : $i, X17 : $i]:
% 58.94/59.19         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X17 @ X15) @ X17) @ X15)
% 58.94/59.19          | ~ (r2_hidden @ X17 @ (k2_relat_1 @ X15)))),
% 58.94/59.19      inference('simplify', [status(thm)], ['17'])).
% 58.94/59.19  thf('19', plain,
% 58.94/59.19      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | (r2_hidden @ 
% 58.94/59.19            (k4_tarski @ (sk_D_1 @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1) @ 
% 58.94/59.19             (sk_C @ sk_B @ sk_C_1)) @ 
% 58.94/59.19            sk_C_1)))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['16', '18'])).
% 58.94/59.19  thf('20', plain,
% 58.94/59.19      (![X15 : $i, X18 : $i]:
% 58.94/59.19         (((X18) = (k2_relat_1 @ X15))
% 58.94/59.19          | (r2_hidden @ 
% 58.94/59.19             (k4_tarski @ (sk_D @ X18 @ X15) @ (sk_C @ X18 @ X15)) @ X15)
% 58.94/59.19          | (r2_hidden @ (sk_C @ X18 @ X15) @ X18))),
% 58.94/59.19      inference('cnf', [status(esa)], [d5_relat_1])).
% 58.94/59.19  thf('21', plain,
% 58.94/59.19      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.94/59.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.94/59.19  thf(t4_subset, axiom,
% 58.94/59.19    (![A:$i,B:$i,C:$i]:
% 58.94/59.19     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 58.94/59.19       ( m1_subset_1 @ A @ C ) ))).
% 58.94/59.19  thf('22', plain,
% 58.94/59.19      (![X7 : $i, X8 : $i, X9 : $i]:
% 58.94/59.19         (~ (r2_hidden @ X7 @ X8)
% 58.94/59.19          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 58.94/59.19          | (m1_subset_1 @ X7 @ X9))),
% 58.94/59.19      inference('cnf', [status(esa)], [t4_subset])).
% 58.94/59.19  thf('23', plain,
% 58.94/59.19      (![X0 : $i]:
% 58.94/59.19         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 58.94/59.19          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 58.94/59.19      inference('sup-', [status(thm)], ['21', '22'])).
% 58.94/59.19  thf('24', plain,
% 58.94/59.19      (![X0 : $i]:
% 58.94/59.19         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 58.94/59.19          | ((X0) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19          | (m1_subset_1 @ 
% 58.94/59.19             (k4_tarski @ (sk_D @ X0 @ sk_C_1) @ (sk_C @ X0 @ sk_C_1)) @ 
% 58.94/59.19             (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.94/59.19      inference('sup-', [status(thm)], ['20', '23'])).
% 58.94/59.19  thf(t2_subset, axiom,
% 58.94/59.19    (![A:$i,B:$i]:
% 58.94/59.19     ( ( m1_subset_1 @ A @ B ) =>
% 58.94/59.19       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 58.94/59.19  thf('25', plain,
% 58.94/59.19      (![X5 : $i, X6 : $i]:
% 58.94/59.19         ((r2_hidden @ X5 @ X6)
% 58.94/59.19          | (v1_xboole_0 @ X6)
% 58.94/59.19          | ~ (m1_subset_1 @ X5 @ X6))),
% 58.94/59.19      inference('cnf', [status(esa)], [t2_subset])).
% 58.94/59.19  thf('26', plain,
% 58.94/59.19      (![X0 : $i]:
% 58.94/59.19         (((X0) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 58.94/59.19          | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 58.94/59.19          | (r2_hidden @ 
% 58.94/59.19             (k4_tarski @ (sk_D @ X0 @ sk_C_1) @ (sk_C @ X0 @ sk_C_1)) @ 
% 58.94/59.19             (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.94/59.19      inference('sup-', [status(thm)], ['24', '25'])).
% 58.94/59.19  thf(l54_zfmisc_1, axiom,
% 58.94/59.19    (![A:$i,B:$i,C:$i,D:$i]:
% 58.94/59.19     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 58.94/59.19       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 58.94/59.19  thf('27', plain,
% 58.94/59.19      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 58.94/59.19         ((r2_hidden @ X2 @ X3)
% 58.94/59.19          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 58.94/59.19      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 58.94/59.19  thf('28', plain,
% 58.94/59.19      (![X0 : $i]:
% 58.94/59.19         ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 58.94/59.19          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 58.94/59.19          | ((X0) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B))),
% 58.94/59.19      inference('sup-', [status(thm)], ['26', '27'])).
% 58.94/59.19  thf('29', plain,
% 58.94/59.19      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | (r2_hidden @ 
% 58.94/59.19            (k4_tarski @ (sk_D_1 @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1) @ 
% 58.94/59.19             (sk_C @ sk_B @ sk_C_1)) @ 
% 58.94/59.19            sk_C_1)))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['16', '18'])).
% 58.94/59.19  thf('30', plain,
% 58.94/59.19      (![X15 : $i, X18 : $i, X19 : $i]:
% 58.94/59.19         (((X18) = (k2_relat_1 @ X15))
% 58.94/59.19          | ~ (r2_hidden @ (k4_tarski @ X19 @ (sk_C @ X18 @ X15)) @ X15)
% 58.94/59.19          | ~ (r2_hidden @ (sk_C @ X18 @ X15) @ X18))),
% 58.94/59.19      inference('cnf', [status(esa)], [d5_relat_1])).
% 58.94/59.19  thf('31', plain,
% 58.94/59.19      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 58.94/59.19         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['29', '30'])).
% 58.94/59.19  thf('32', plain,
% 58.94/59.19      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 58.94/59.19         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('simplify', [status(thm)], ['31'])).
% 58.94/59.19  thf('33', plain,
% 58.94/59.19      ((((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 58.94/59.19         | ((sk_B) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 58.94/59.19         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['28', '32'])).
% 58.94/59.19  thf('34', plain,
% 58.94/59.19      ((((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 58.94/59.19         | ((sk_B) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('simplify', [status(thm)], ['33'])).
% 58.94/59.19  thf('35', plain,
% 58.94/59.19      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 58.94/59.19         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('simplify', [status(thm)], ['31'])).
% 58.94/59.19  thf('36', plain,
% 58.94/59.19      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 58.94/59.19         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('clc', [status(thm)], ['34', '35'])).
% 58.94/59.19  thf('37', plain,
% 58.94/59.19      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 58.94/59.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.94/59.19  thf(t5_subset, axiom,
% 58.94/59.19    (![A:$i,B:$i,C:$i]:
% 58.94/59.19     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 58.94/59.19          ( v1_xboole_0 @ C ) ) ))).
% 58.94/59.19  thf('38', plain,
% 58.94/59.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 58.94/59.19         (~ (r2_hidden @ X10 @ X11)
% 58.94/59.19          | ~ (v1_xboole_0 @ X12)
% 58.94/59.19          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 58.94/59.19      inference('cnf', [status(esa)], [t5_subset])).
% 58.94/59.19  thf('39', plain,
% 58.94/59.19      (![X0 : $i]:
% 58.94/59.19         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 58.94/59.19          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 58.94/59.19      inference('sup-', [status(thm)], ['37', '38'])).
% 58.94/59.19  thf('40', plain,
% 58.94/59.19      ((![X0 : $i]:
% 58.94/59.19          (((sk_B) = (k2_relat_1 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['36', '39'])).
% 58.94/59.19  thf('41', plain,
% 58.94/59.19      (((((sk_B) = (k2_relat_1 @ sk_C_1)) | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['19', '40'])).
% 58.94/59.19  thf('42', plain,
% 58.94/59.19      ((((sk_B) = (k2_relat_1 @ sk_C_1)))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('simplify', [status(thm)], ['41'])).
% 58.94/59.19  thf('43', plain,
% 58.94/59.19      (![X23 : $i]:
% 58.94/59.19         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 58.94/59.19          | ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_1))),
% 58.94/59.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 58.94/59.19  thf('44', plain,
% 58.94/59.19      (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 58.94/59.19       (![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_1))),
% 58.94/59.19      inference('split', [status(esa)], ['43'])).
% 58.94/59.19  thf('45', plain,
% 58.94/59.19      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 58.94/59.19      inference('split', [status(esa)], ['0'])).
% 58.94/59.19  thf('46', plain,
% 58.94/59.19      ((![X24 : $i]:
% 58.94/59.19          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19           | ~ (r2_hidden @ X24 @ sk_B)))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('split', [status(esa)], ['9'])).
% 58.94/59.19  thf('47', plain,
% 58.94/59.19      (((r2_hidden @ (k4_tarski @ (sk_E @ sk_D_2) @ sk_D_2) @ sk_C_1))
% 58.94/59.19         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 58.94/59.19             (![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['45', '46'])).
% 58.94/59.19  thf('48', plain,
% 58.94/59.19      ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_1))
% 58.94/59.19         <= ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_1)))),
% 58.94/59.19      inference('split', [status(esa)], ['43'])).
% 58.94/59.19  thf('49', plain,
% 58.94/59.19      (~ ((r2_hidden @ sk_D_2 @ sk_B)) | 
% 58.94/59.19       ~ (![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_1)) | 
% 58.94/59.19       ~
% 58.94/59.19       (![X24 : $i]:
% 58.94/59.19          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19           | ~ (r2_hidden @ X24 @ sk_B)))),
% 58.94/59.19      inference('sup-', [status(thm)], ['47', '48'])).
% 58.94/59.19  thf('50', plain,
% 58.94/59.19      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 58.94/59.19      inference('split', [status(esa)], ['0'])).
% 58.94/59.19  thf('51', plain,
% 58.94/59.19      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 58.94/59.19      inference('sup-', [status(thm)], ['2', '3'])).
% 58.94/59.19  thf('52', plain,
% 58.94/59.19      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))
% 58.94/59.19         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 58.94/59.19      inference('split', [status(esa)], ['9'])).
% 58.94/59.19  thf('53', plain,
% 58.94/59.19      ((((k2_relat_1 @ sk_C_1) = (sk_B)))
% 58.94/59.19         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 58.94/59.19      inference('sup+', [status(thm)], ['51', '52'])).
% 58.94/59.19  thf('54', plain,
% 58.94/59.19      (![X15 : $i, X17 : $i]:
% 58.94/59.19         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X17 @ X15) @ X17) @ X15)
% 58.94/59.19          | ~ (r2_hidden @ X17 @ (k2_relat_1 @ X15)))),
% 58.94/59.19      inference('simplify', [status(thm)], ['17'])).
% 58.94/59.19  thf('55', plain,
% 58.94/59.19      ((![X0 : $i]:
% 58.94/59.19          (~ (r2_hidden @ X0 @ sk_B)
% 58.94/59.19           | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_C_1) @ X0) @ sk_C_1)))
% 58.94/59.19         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['53', '54'])).
% 58.94/59.19  thf('56', plain,
% 58.94/59.19      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_D_2) @ sk_C_1))
% 58.94/59.19         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 58.94/59.19             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['50', '55'])).
% 58.94/59.19  thf('57', plain,
% 58.94/59.19      ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_1))
% 58.94/59.19         <= ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_1)))),
% 58.94/59.19      inference('split', [status(esa)], ['43'])).
% 58.94/59.19  thf('58', plain,
% 58.94/59.19      (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 58.94/59.19       ~ (![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_1)) | 
% 58.94/59.19       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 58.94/59.19      inference('sup-', [status(thm)], ['56', '57'])).
% 58.94/59.19  thf('59', plain,
% 58.94/59.19      (((r2_hidden @ (k4_tarski @ (sk_E @ sk_D_2) @ sk_D_2) @ sk_C_1))
% 58.94/59.19         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 58.94/59.19             (![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['45', '46'])).
% 58.94/59.19  thf('60', plain,
% 58.94/59.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 58.94/59.19         ((r2_hidden @ X14 @ (k2_relat_1 @ X15))
% 58.94/59.19          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15))),
% 58.94/59.19      inference('simplify', [status(thm)], ['6'])).
% 58.94/59.19  thf('61', plain,
% 58.94/59.19      (((r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_1)))
% 58.94/59.19         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 58.94/59.19             (![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['59', '60'])).
% 58.94/59.19  thf('62', plain,
% 58.94/59.19      (![X15 : $i, X17 : $i]:
% 58.94/59.19         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X17 @ X15) @ X17) @ X15)
% 58.94/59.19          | ~ (r2_hidden @ X17 @ (k2_relat_1 @ X15)))),
% 58.94/59.19      inference('simplify', [status(thm)], ['17'])).
% 58.94/59.19  thf('63', plain,
% 58.94/59.19      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_D_2) @ sk_C_1))
% 58.94/59.19         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 58.94/59.19             (![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['61', '62'])).
% 58.94/59.19  thf('64', plain,
% 58.94/59.19      ((![X0 : $i]:
% 58.94/59.19          (((sk_B) = (k2_relat_1 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 58.94/59.19         <= ((![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['36', '39'])).
% 58.94/59.19  thf('65', plain,
% 58.94/59.19      ((((sk_B) = (k2_relat_1 @ sk_C_1)))
% 58.94/59.19         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 58.94/59.19             (![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['63', '64'])).
% 58.94/59.19  thf('66', plain,
% 58.94/59.19      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 58.94/59.19      inference('sup-', [status(thm)], ['2', '3'])).
% 58.94/59.19  thf('67', plain,
% 58.94/59.19      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B)))
% 58.94/59.19         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 58.94/59.19      inference('split', [status(esa)], ['0'])).
% 58.94/59.19  thf('68', plain,
% 58.94/59.19      ((((k2_relat_1 @ sk_C_1) != (sk_B)))
% 58.94/59.19         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['66', '67'])).
% 58.94/59.19  thf('69', plain,
% 58.94/59.19      ((((sk_B) != (sk_B)))
% 58.94/59.19         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 58.94/59.19             ((r2_hidden @ sk_D_2 @ sk_B)) & 
% 58.94/59.19             (![X24 : $i]:
% 58.94/59.19                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 58.94/59.19      inference('sup-', [status(thm)], ['65', '68'])).
% 58.94/59.19  thf('70', plain,
% 58.94/59.19      (~ ((r2_hidden @ sk_D_2 @ sk_B)) | 
% 58.94/59.19       ~
% 58.94/59.19       (![X24 : $i]:
% 58.94/59.19          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19           | ~ (r2_hidden @ X24 @ sk_B))) | 
% 58.94/59.19       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 58.94/59.19      inference('simplify', [status(thm)], ['69'])).
% 58.94/59.19  thf('71', plain,
% 58.94/59.19      (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 58.94/59.19       ((r2_hidden @ sk_D_2 @ sk_B))),
% 58.94/59.19      inference('split', [status(esa)], ['0'])).
% 58.94/59.19  thf('72', plain,
% 58.94/59.19      ((![X24 : $i]:
% 58.94/59.19          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19           | ~ (r2_hidden @ X24 @ sk_B))) | 
% 58.94/59.19       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 58.94/59.19      inference('split', [status(esa)], ['9'])).
% 58.94/59.19  thf('73', plain,
% 58.94/59.19      ((![X24 : $i]:
% 58.94/59.19          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_1)
% 58.94/59.19           | ~ (r2_hidden @ X24 @ sk_B)))),
% 58.94/59.19      inference('sat_resolution*', [status(thm)],
% 58.94/59.19                ['44', '49', '58', '70', '71', '72'])).
% 58.94/59.19  thf('74', plain, (((sk_B) = (k2_relat_1 @ sk_C_1))),
% 58.94/59.19      inference('simpl_trail', [status(thm)], ['42', '73'])).
% 58.94/59.19  thf('75', plain,
% 58.94/59.19      ((((sk_B) != (sk_B)))
% 58.94/59.19         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 58.94/59.19      inference('demod', [status(thm)], ['1', '4', '74'])).
% 58.94/59.19  thf('76', plain,
% 58.94/59.19      (($false) <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 58.94/59.19      inference('simplify', [status(thm)], ['75'])).
% 58.94/59.19  thf('77', plain, (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 58.94/59.19      inference('sat_resolution*', [status(thm)],
% 58.94/59.19                ['44', '49', '58', '72', '70', '71'])).
% 58.94/59.19  thf('78', plain, ($false),
% 58.94/59.19      inference('simpl_trail', [status(thm)], ['76', '77'])).
% 58.94/59.19  
% 58.94/59.19  % SZS output end Refutation
% 58.94/59.19  
% 58.94/59.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
