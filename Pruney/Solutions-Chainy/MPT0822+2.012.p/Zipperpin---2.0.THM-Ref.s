%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WT4hKgkHVd

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:59 EST 2020

% Result     : Theorem 33.84s
% Output     : Refutation 33.84s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 141 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  807 (1915 expanded)
%              Number of equality atoms :   51 ( 116 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X19: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X10 ) @ ( sk_C @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ sk_C_1 ) @ ( sk_C @ X0 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X10 ) @ ( sk_C @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k2_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ ( k2_relat_1 @ X0 ) )
        | ( sk_B
          = ( k2_relat_1 @ X0 ) )
        | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ sk_B @ X0 ) ) @ ( sk_C @ sk_B @ X0 ) ) @ sk_C_1 ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_C @ X13 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('18',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('21',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ( X11
       != ( k2_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('23',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) @ ( sk_C @ sk_B @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_C @ X13 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('26',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf('29',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('31',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X19: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X19 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ~ ! [X19: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X19 ) @ X19 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X19 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X18: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ sk_D_2 ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X18: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X18 @ sk_D_2 ) @ sk_C_1 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('43',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_1 ) @ X0 ) @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ! [X18: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X18 @ sk_D_2 ) @ sk_C_1 )
   <= ! [X18: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X18 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['39'])).

thf('49',plain,
    ( ~ ! [X18: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X18 @ sk_D_2 ) @ sk_C_1 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','38','40','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WT4hKgkHVd
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 13:56:45 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.32  % Running in FO mode
% 33.84/34.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 33.84/34.04  % Solved by: fo/fo7.sh
% 33.84/34.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 33.84/34.04  % done 6080 iterations in 33.609s
% 33.84/34.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 33.84/34.04  % SZS output start Refutation
% 33.84/34.04  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 33.84/34.04  thf(sk_E_type, type, sk_E: $i > $i).
% 33.84/34.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 33.84/34.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 33.84/34.04  thf(sk_D_2_type, type, sk_D_2: $i).
% 33.84/34.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 33.84/34.04  thf(sk_B_type, type, sk_B: $i).
% 33.84/34.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 33.84/34.04  thf(sk_A_type, type, sk_A: $i).
% 33.84/34.04  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 33.84/34.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 33.84/34.04  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 33.84/34.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 33.84/34.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 33.84/34.04  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 33.84/34.04  thf(t23_relset_1, conjecture,
% 33.84/34.04    (![A:$i,B:$i,C:$i]:
% 33.84/34.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.84/34.04       ( ( ![D:$i]:
% 33.84/34.04           ( ~( ( r2_hidden @ D @ B ) & 
% 33.84/34.04                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 33.84/34.04         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 33.84/34.04  thf(zf_stmt_0, negated_conjecture,
% 33.84/34.04    (~( ![A:$i,B:$i,C:$i]:
% 33.84/34.04        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.84/34.04          ( ( ![D:$i]:
% 33.84/34.04              ( ~( ( r2_hidden @ D @ B ) & 
% 33.84/34.04                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 33.84/34.04            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 33.84/34.04    inference('cnf.neg', [status(esa)], [t23_relset_1])).
% 33.84/34.04  thf('0', plain,
% 33.84/34.04      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 33.84/34.04        | (r2_hidden @ sk_D_2 @ sk_B))),
% 33.84/34.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.84/34.04  thf('1', plain,
% 33.84/34.04      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 33.84/34.04       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 33.84/34.04      inference('split', [status(esa)], ['0'])).
% 33.84/34.04  thf('2', plain,
% 33.84/34.04      (![X19 : $i]:
% 33.84/34.04         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))
% 33.84/34.04          | (r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04          | ~ (r2_hidden @ X19 @ sk_B))),
% 33.84/34.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.84/34.04  thf('3', plain,
% 33.84/34.04      ((![X19 : $i]:
% 33.84/34.04          ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04           | ~ (r2_hidden @ X19 @ sk_B))) | 
% 33.84/34.04       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 33.84/34.04      inference('split', [status(esa)], ['2'])).
% 33.84/34.04  thf(d5_relat_1, axiom,
% 33.84/34.04    (![A:$i,B:$i]:
% 33.84/34.04     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 33.84/34.04       ( ![C:$i]:
% 33.84/34.04         ( ( r2_hidden @ C @ B ) <=>
% 33.84/34.04           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 33.84/34.04  thf('4', plain,
% 33.84/34.04      (![X10 : $i, X13 : $i]:
% 33.84/34.04         (((X13) = (k2_relat_1 @ X10))
% 33.84/34.04          | (r2_hidden @ 
% 33.84/34.04             (k4_tarski @ (sk_D @ X13 @ X10) @ (sk_C @ X13 @ X10)) @ X10)
% 33.84/34.04          | (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 33.84/34.04      inference('cnf', [status(esa)], [d5_relat_1])).
% 33.84/34.04  thf('5', plain,
% 33.84/34.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.84/34.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.84/34.04  thf(l3_subset_1, axiom,
% 33.84/34.04    (![A:$i,B:$i]:
% 33.84/34.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 33.84/34.04       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 33.84/34.04  thf('6', plain,
% 33.84/34.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 33.84/34.04         (~ (r2_hidden @ X5 @ X6)
% 33.84/34.04          | (r2_hidden @ X5 @ X7)
% 33.84/34.04          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 33.84/34.04      inference('cnf', [status(esa)], [l3_subset_1])).
% 33.84/34.04  thf('7', plain,
% 33.84/34.04      (![X0 : $i]:
% 33.84/34.04         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 33.84/34.04          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 33.84/34.04      inference('sup-', [status(thm)], ['5', '6'])).
% 33.84/34.04  thf('8', plain,
% 33.84/34.04      (![X0 : $i]:
% 33.84/34.04         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 33.84/34.04          | ((X0) = (k2_relat_1 @ sk_C_1))
% 33.84/34.04          | (r2_hidden @ 
% 33.84/34.04             (k4_tarski @ (sk_D @ X0 @ sk_C_1) @ (sk_C @ X0 @ sk_C_1)) @ 
% 33.84/34.04             (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.84/34.04      inference('sup-', [status(thm)], ['4', '7'])).
% 33.84/34.04  thf(l54_zfmisc_1, axiom,
% 33.84/34.04    (![A:$i,B:$i,C:$i,D:$i]:
% 33.84/34.04     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 33.84/34.04       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 33.84/34.04  thf('9', plain,
% 33.84/34.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 33.84/34.04         ((r2_hidden @ X2 @ X3)
% 33.84/34.04          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 33.84/34.04      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 33.84/34.04  thf('10', plain,
% 33.84/34.04      (![X0 : $i]:
% 33.84/34.04         (((X0) = (k2_relat_1 @ sk_C_1))
% 33.84/34.04          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 33.84/34.04          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B))),
% 33.84/34.04      inference('sup-', [status(thm)], ['8', '9'])).
% 33.84/34.04  thf('11', plain,
% 33.84/34.04      (![X10 : $i, X13 : $i]:
% 33.84/34.04         (((X13) = (k2_relat_1 @ X10))
% 33.84/34.04          | (r2_hidden @ 
% 33.84/34.04             (k4_tarski @ (sk_D @ X13 @ X10) @ (sk_C @ X13 @ X10)) @ X10)
% 33.84/34.04          | (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 33.84/34.04      inference('cnf', [status(esa)], [d5_relat_1])).
% 33.84/34.04  thf('12', plain,
% 33.84/34.04      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 33.84/34.04         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 33.84/34.04          | (r2_hidden @ X9 @ X11)
% 33.84/34.04          | ((X11) != (k2_relat_1 @ X10)))),
% 33.84/34.04      inference('cnf', [status(esa)], [d5_relat_1])).
% 33.84/34.04  thf('13', plain,
% 33.84/34.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 33.84/34.04         ((r2_hidden @ X9 @ (k2_relat_1 @ X10))
% 33.84/34.04          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 33.84/34.04      inference('simplify', [status(thm)], ['12'])).
% 33.84/34.04  thf('14', plain,
% 33.84/34.04      (![X0 : $i, X1 : $i]:
% 33.84/34.04         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 33.84/34.04          | ((X1) = (k2_relat_1 @ X0))
% 33.84/34.04          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 33.84/34.04      inference('sup-', [status(thm)], ['11', '13'])).
% 33.84/34.04  thf('15', plain,
% 33.84/34.04      ((![X19 : $i]:
% 33.84/34.04          ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04           | ~ (r2_hidden @ X19 @ sk_B)))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('split', [status(esa)], ['2'])).
% 33.84/34.04  thf('16', plain,
% 33.84/34.04      ((![X0 : $i]:
% 33.84/34.04          ((r2_hidden @ (sk_C @ sk_B @ X0) @ (k2_relat_1 @ X0))
% 33.84/34.04           | ((sk_B) = (k2_relat_1 @ X0))
% 33.84/34.04           | (r2_hidden @ 
% 33.84/34.04              (k4_tarski @ (sk_E @ (sk_C @ sk_B @ X0)) @ (sk_C @ sk_B @ X0)) @ 
% 33.84/34.04              sk_C_1)))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('sup-', [status(thm)], ['14', '15'])).
% 33.84/34.04  thf('17', plain,
% 33.84/34.04      (![X10 : $i, X13 : $i, X14 : $i]:
% 33.84/34.04         (((X13) = (k2_relat_1 @ X10))
% 33.84/34.04          | ~ (r2_hidden @ (k4_tarski @ X14 @ (sk_C @ X13 @ X10)) @ X10)
% 33.84/34.04          | ~ (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 33.84/34.04      inference('cnf', [status(esa)], [d5_relat_1])).
% 33.84/34.04  thf('18', plain,
% 33.84/34.04      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 33.84/34.04         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 33.84/34.04         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 33.84/34.04         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('sup-', [status(thm)], ['16', '17'])).
% 33.84/34.04  thf('19', plain,
% 33.84/34.04      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 33.84/34.04         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 33.84/34.04         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('simplify', [status(thm)], ['18'])).
% 33.84/34.04  thf('20', plain,
% 33.84/34.04      (![X0 : $i, X1 : $i]:
% 33.84/34.04         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 33.84/34.04          | ((X1) = (k2_relat_1 @ X0))
% 33.84/34.04          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 33.84/34.04      inference('sup-', [status(thm)], ['11', '13'])).
% 33.84/34.04  thf('21', plain,
% 33.84/34.04      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 33.84/34.04         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k2_relat_1 @ sk_C_1))))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('clc', [status(thm)], ['19', '20'])).
% 33.84/34.04  thf('22', plain,
% 33.84/34.04      (![X10 : $i, X11 : $i, X12 : $i]:
% 33.84/34.04         (~ (r2_hidden @ X12 @ X11)
% 33.84/34.04          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X12 @ X10) @ X12) @ X10)
% 33.84/34.04          | ((X11) != (k2_relat_1 @ X10)))),
% 33.84/34.04      inference('cnf', [status(esa)], [d5_relat_1])).
% 33.84/34.04  thf('23', plain,
% 33.84/34.04      (![X10 : $i, X12 : $i]:
% 33.84/34.04         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X12 @ X10) @ X12) @ X10)
% 33.84/34.04          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X10)))),
% 33.84/34.04      inference('simplify', [status(thm)], ['22'])).
% 33.84/34.04  thf('24', plain,
% 33.84/34.04      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 33.84/34.04         | (r2_hidden @ 
% 33.84/34.04            (k4_tarski @ (sk_D_1 @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1) @ 
% 33.84/34.04             (sk_C @ sk_B @ sk_C_1)) @ 
% 33.84/34.04            sk_C_1)))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('sup-', [status(thm)], ['21', '23'])).
% 33.84/34.04  thf('25', plain,
% 33.84/34.04      (![X10 : $i, X13 : $i, X14 : $i]:
% 33.84/34.04         (((X13) = (k2_relat_1 @ X10))
% 33.84/34.04          | ~ (r2_hidden @ (k4_tarski @ X14 @ (sk_C @ X13 @ X10)) @ X10)
% 33.84/34.04          | ~ (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 33.84/34.04      inference('cnf', [status(esa)], [d5_relat_1])).
% 33.84/34.04  thf('26', plain,
% 33.84/34.04      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 33.84/34.04         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 33.84/34.04         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('sup-', [status(thm)], ['24', '25'])).
% 33.84/34.04  thf('27', plain,
% 33.84/34.04      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 33.84/34.04         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('simplify', [status(thm)], ['26'])).
% 33.84/34.04  thf('28', plain,
% 33.84/34.04      ((((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 33.84/34.04         | ((sk_B) = (k2_relat_1 @ sk_C_1))
% 33.84/34.04         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('sup-', [status(thm)], ['10', '27'])).
% 33.84/34.04  thf('29', plain,
% 33.84/34.04      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 33.84/34.04         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('simplify', [status(thm)], ['28'])).
% 33.84/34.04  thf('30', plain,
% 33.84/34.04      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 33.84/34.04         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('simplify', [status(thm)], ['26'])).
% 33.84/34.04  thf('31', plain,
% 33.84/34.04      ((((sk_B) = (k2_relat_1 @ sk_C_1)))
% 33.84/34.04         <= ((![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('clc', [status(thm)], ['29', '30'])).
% 33.84/34.04  thf('32', plain,
% 33.84/34.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.84/34.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.84/34.04  thf(redefinition_k2_relset_1, axiom,
% 33.84/34.04    (![A:$i,B:$i,C:$i]:
% 33.84/34.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.84/34.04       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 33.84/34.04  thf('33', plain,
% 33.84/34.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 33.84/34.04         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 33.84/34.04          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 33.84/34.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 33.84/34.04  thf('34', plain,
% 33.84/34.04      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 33.84/34.04      inference('sup-', [status(thm)], ['32', '33'])).
% 33.84/34.04  thf('35', plain,
% 33.84/34.04      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B)))
% 33.84/34.04         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 33.84/34.04      inference('split', [status(esa)], ['0'])).
% 33.84/34.04  thf('36', plain,
% 33.84/34.04      ((((k2_relat_1 @ sk_C_1) != (sk_B)))
% 33.84/34.04         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 33.84/34.04      inference('sup-', [status(thm)], ['34', '35'])).
% 33.84/34.04  thf('37', plain,
% 33.84/34.04      ((((sk_B) != (sk_B)))
% 33.84/34.04         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 33.84/34.04             (![X19 : $i]:
% 33.84/34.04                ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 33.84/34.04      inference('sup-', [status(thm)], ['31', '36'])).
% 33.84/34.04  thf('38', plain,
% 33.84/34.04      (~
% 33.84/34.04       (![X19 : $i]:
% 33.84/34.04          ((r2_hidden @ (k4_tarski @ (sk_E @ X19) @ X19) @ sk_C_1)
% 33.84/34.04           | ~ (r2_hidden @ X19 @ sk_B))) | 
% 33.84/34.04       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 33.84/34.04      inference('simplify', [status(thm)], ['37'])).
% 33.84/34.04  thf('39', plain,
% 33.84/34.04      (![X18 : $i]:
% 33.84/34.04         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 33.84/34.04          | ~ (r2_hidden @ (k4_tarski @ X18 @ sk_D_2) @ sk_C_1))),
% 33.84/34.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.84/34.04  thf('40', plain,
% 33.84/34.04      ((![X18 : $i]: ~ (r2_hidden @ (k4_tarski @ X18 @ sk_D_2) @ sk_C_1)) | 
% 33.84/34.04       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 33.84/34.04      inference('split', [status(esa)], ['39'])).
% 33.84/34.04  thf('41', plain,
% 33.84/34.04      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 33.84/34.04      inference('split', [status(esa)], ['0'])).
% 33.84/34.04  thf('42', plain,
% 33.84/34.04      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 33.84/34.04      inference('sup-', [status(thm)], ['32', '33'])).
% 33.84/34.04  thf('43', plain,
% 33.84/34.04      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))
% 33.84/34.04         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 33.84/34.04      inference('split', [status(esa)], ['2'])).
% 33.84/34.04  thf('44', plain,
% 33.84/34.04      ((((k2_relat_1 @ sk_C_1) = (sk_B)))
% 33.84/34.04         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 33.84/34.04      inference('sup+', [status(thm)], ['42', '43'])).
% 33.84/34.04  thf('45', plain,
% 33.84/34.04      (![X10 : $i, X12 : $i]:
% 33.84/34.04         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X12 @ X10) @ X12) @ X10)
% 33.84/34.04          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X10)))),
% 33.84/34.04      inference('simplify', [status(thm)], ['22'])).
% 33.84/34.04  thf('46', plain,
% 33.84/34.04      ((![X0 : $i]:
% 33.84/34.04          (~ (r2_hidden @ X0 @ sk_B)
% 33.84/34.04           | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_C_1) @ X0) @ sk_C_1)))
% 33.84/34.04         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 33.84/34.04      inference('sup-', [status(thm)], ['44', '45'])).
% 33.84/34.04  thf('47', plain,
% 33.84/34.04      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_D_2) @ sk_C_1))
% 33.84/34.04         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 33.84/34.04             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 33.84/34.04      inference('sup-', [status(thm)], ['41', '46'])).
% 33.84/34.04  thf('48', plain,
% 33.84/34.04      ((![X18 : $i]: ~ (r2_hidden @ (k4_tarski @ X18 @ sk_D_2) @ sk_C_1))
% 33.84/34.04         <= ((![X18 : $i]: ~ (r2_hidden @ (k4_tarski @ X18 @ sk_D_2) @ sk_C_1)))),
% 33.84/34.04      inference('split', [status(esa)], ['39'])).
% 33.84/34.04  thf('49', plain,
% 33.84/34.04      (~ (![X18 : $i]: ~ (r2_hidden @ (k4_tarski @ X18 @ sk_D_2) @ sk_C_1)) | 
% 33.84/34.04       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 33.84/34.04       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 33.84/34.04      inference('sup-', [status(thm)], ['47', '48'])).
% 33.84/34.04  thf('50', plain, ($false),
% 33.84/34.04      inference('sat_resolution*', [status(thm)], ['1', '3', '38', '40', '49'])).
% 33.84/34.04  
% 33.84/34.04  % SZS output end Refutation
% 33.84/34.04  
% 33.84/34.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
