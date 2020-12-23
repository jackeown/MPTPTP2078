%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uarhZxrIu1

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:57 EST 2020

% Result     : Theorem 8.08s
% Output     : Refutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 133 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  765 (1787 expanded)
%              Number of equality atoms :   47 ( 106 expanded)
%              Maximal formula depth    :   16 (   7 average)

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

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t22_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
        <=> ( ( k1_relset_1 @ B @ A @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_relset_1])).

thf('0',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X19: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X10 ) @ ( sk_D @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k1_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ( sk_B
          = ( k1_relat_1 @ X0 ) )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ X0 ) @ ( sk_E @ ( sk_C @ sk_B @ X0 ) ) ) @ sk_C_1 ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X10 ) @ X14 ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('11',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('14',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D_1 @ X12 @ X10 ) ) @ X10 )
      | ( X11
       != ( k1_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('16',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D_1 @ X12 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_C_1 ) @ ( sk_D_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_C_1 ) @ ( sk_D_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_C_1 ) @ ( sk_D_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('25',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X10 ) @ X14 ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('26',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ! [X19: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X19 @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
       != sk_B )
      & ! [X19: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
          | ~ ( r2_hidden @ X19 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ~ ! [X19: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_E @ X19 ) ) @ sk_C_1 )
          | ~ ( r2_hidden @ X19 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X18: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X18 ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X18: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X18 ) @ sk_C_1 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('40',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D_1 @ X12 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ! [X18: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X18 ) @ sk_C_1 )
   <= ! [X18: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X18 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('46',plain,
    ( ~ ! [X18: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X18 ) @ sk_C_1 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','35','37','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uarhZxrIu1
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.08/8.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.08/8.29  % Solved by: fo/fo7.sh
% 8.08/8.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.08/8.29  % done 1844 iterations in 7.832s
% 8.08/8.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.08/8.29  % SZS output start Refutation
% 8.08/8.29  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 8.08/8.29  thf(sk_E_type, type, sk_E: $i > $i).
% 8.08/8.29  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.08/8.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.08/8.29  thf(sk_D_2_type, type, sk_D_2: $i).
% 8.08/8.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.08/8.29  thf(sk_B_type, type, sk_B: $i).
% 8.08/8.29  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.08/8.29  thf(sk_A_type, type, sk_A: $i).
% 8.08/8.29  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 8.08/8.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.08/8.29  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 8.08/8.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.08/8.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.08/8.29  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 8.08/8.29  thf(t22_relset_1, conjecture,
% 8.08/8.29    (![A:$i,B:$i,C:$i]:
% 8.08/8.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 8.08/8.29       ( ( ![D:$i]:
% 8.08/8.29           ( ~( ( r2_hidden @ D @ B ) & 
% 8.08/8.29                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 8.08/8.29         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 8.08/8.29  thf(zf_stmt_0, negated_conjecture,
% 8.08/8.29    (~( ![A:$i,B:$i,C:$i]:
% 8.08/8.29        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 8.08/8.29          ( ( ![D:$i]:
% 8.08/8.29              ( ~( ( r2_hidden @ D @ B ) & 
% 8.08/8.29                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 8.08/8.29            ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ) )),
% 8.08/8.29    inference('cnf.neg', [status(esa)], [t22_relset_1])).
% 8.08/8.29  thf('0', plain,
% 8.08/8.29      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) != (sk_B))
% 8.08/8.29        | (r2_hidden @ sk_D_2 @ sk_B))),
% 8.08/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.08/8.29  thf('1', plain,
% 8.08/8.29      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 8.08/8.29       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))),
% 8.08/8.29      inference('split', [status(esa)], ['0'])).
% 8.08/8.29  thf('2', plain,
% 8.08/8.29      (![X19 : $i]:
% 8.08/8.29         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))
% 8.08/8.29          | (r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29          | ~ (r2_hidden @ X19 @ sk_B))),
% 8.08/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.08/8.29  thf('3', plain,
% 8.08/8.29      ((![X19 : $i]:
% 8.08/8.29          ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29           | ~ (r2_hidden @ X19 @ sk_B))) | 
% 8.08/8.29       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))),
% 8.08/8.29      inference('split', [status(esa)], ['2'])).
% 8.08/8.29  thf(d4_relat_1, axiom,
% 8.08/8.29    (![A:$i,B:$i]:
% 8.08/8.29     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 8.08/8.29       ( ![C:$i]:
% 8.08/8.29         ( ( r2_hidden @ C @ B ) <=>
% 8.08/8.29           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 8.08/8.29  thf('4', plain,
% 8.08/8.29      (![X10 : $i, X13 : $i]:
% 8.08/8.29         (((X13) = (k1_relat_1 @ X10))
% 8.08/8.29          | (r2_hidden @ 
% 8.08/8.29             (k4_tarski @ (sk_C @ X13 @ X10) @ (sk_D @ X13 @ X10)) @ X10)
% 8.08/8.29          | (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 8.08/8.29      inference('cnf', [status(esa)], [d4_relat_1])).
% 8.08/8.29  thf('5', plain,
% 8.08/8.29      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 8.08/8.29         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 8.08/8.29          | (r2_hidden @ X8 @ X11)
% 8.08/8.29          | ((X11) != (k1_relat_1 @ X10)))),
% 8.08/8.29      inference('cnf', [status(esa)], [d4_relat_1])).
% 8.08/8.29  thf('6', plain,
% 8.08/8.29      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.08/8.29         ((r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 8.08/8.29          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 8.08/8.29      inference('simplify', [status(thm)], ['5'])).
% 8.08/8.29  thf('7', plain,
% 8.08/8.29      (![X0 : $i, X1 : $i]:
% 8.08/8.29         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 8.08/8.29          | ((X1) = (k1_relat_1 @ X0))
% 8.08/8.29          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 8.08/8.29      inference('sup-', [status(thm)], ['4', '6'])).
% 8.08/8.29  thf('8', plain,
% 8.08/8.29      ((![X19 : $i]:
% 8.08/8.29          ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29           | ~ (r2_hidden @ X19 @ sk_B)))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('split', [status(esa)], ['2'])).
% 8.08/8.29  thf('9', plain,
% 8.08/8.29      ((![X0 : $i]:
% 8.08/8.29          ((r2_hidden @ (sk_C @ sk_B @ X0) @ (k1_relat_1 @ X0))
% 8.08/8.29           | ((sk_B) = (k1_relat_1 @ X0))
% 8.08/8.29           | (r2_hidden @ 
% 8.08/8.29              (k4_tarski @ (sk_C @ sk_B @ X0) @ (sk_E @ (sk_C @ sk_B @ X0))) @ 
% 8.08/8.29              sk_C_1)))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['7', '8'])).
% 8.08/8.29  thf('10', plain,
% 8.08/8.29      (![X10 : $i, X13 : $i, X14 : $i]:
% 8.08/8.29         (((X13) = (k1_relat_1 @ X10))
% 8.08/8.29          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X13 @ X10) @ X14) @ X10)
% 8.08/8.29          | ~ (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 8.08/8.29      inference('cnf', [status(esa)], [d4_relat_1])).
% 8.08/8.29  thf('11', plain,
% 8.08/8.29      (((((sk_B) = (k1_relat_1 @ sk_C_1))
% 8.08/8.29         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 8.08/8.29         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 8.08/8.29         | ((sk_B) = (k1_relat_1 @ sk_C_1))))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['9', '10'])).
% 8.08/8.29  thf('12', plain,
% 8.08/8.29      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 8.08/8.29         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 8.08/8.29         | ((sk_B) = (k1_relat_1 @ sk_C_1))))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('simplify', [status(thm)], ['11'])).
% 8.08/8.29  thf('13', plain,
% 8.08/8.29      (![X0 : $i, X1 : $i]:
% 8.08/8.29         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 8.08/8.29          | ((X1) = (k1_relat_1 @ X0))
% 8.08/8.29          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 8.08/8.29      inference('sup-', [status(thm)], ['4', '6'])).
% 8.08/8.29  thf('14', plain,
% 8.08/8.29      (((((sk_B) = (k1_relat_1 @ sk_C_1))
% 8.08/8.29         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k1_relat_1 @ sk_C_1))))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('clc', [status(thm)], ['12', '13'])).
% 8.08/8.29  thf('15', plain,
% 8.08/8.29      (![X10 : $i, X11 : $i, X12 : $i]:
% 8.08/8.29         (~ (r2_hidden @ X12 @ X11)
% 8.08/8.29          | (r2_hidden @ (k4_tarski @ X12 @ (sk_D_1 @ X12 @ X10)) @ X10)
% 8.08/8.29          | ((X11) != (k1_relat_1 @ X10)))),
% 8.08/8.29      inference('cnf', [status(esa)], [d4_relat_1])).
% 8.08/8.29  thf('16', plain,
% 8.08/8.29      (![X10 : $i, X12 : $i]:
% 8.08/8.29         ((r2_hidden @ (k4_tarski @ X12 @ (sk_D_1 @ X12 @ X10)) @ X10)
% 8.08/8.29          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X10)))),
% 8.08/8.29      inference('simplify', [status(thm)], ['15'])).
% 8.08/8.29  thf('17', plain,
% 8.08/8.29      (((((sk_B) = (k1_relat_1 @ sk_C_1))
% 8.08/8.29         | (r2_hidden @ 
% 8.08/8.29            (k4_tarski @ (sk_C @ sk_B @ sk_C_1) @ 
% 8.08/8.29             (sk_D_1 @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)) @ 
% 8.08/8.29            sk_C_1)))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['14', '16'])).
% 8.08/8.29  thf('18', plain,
% 8.08/8.29      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.08/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.08/8.29  thf(l3_subset_1, axiom,
% 8.08/8.29    (![A:$i,B:$i]:
% 8.08/8.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.08/8.29       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 8.08/8.29  thf('19', plain,
% 8.08/8.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 8.08/8.29         (~ (r2_hidden @ X5 @ X6)
% 8.08/8.29          | (r2_hidden @ X5 @ X7)
% 8.08/8.29          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 8.08/8.29      inference('cnf', [status(esa)], [l3_subset_1])).
% 8.08/8.29  thf('20', plain,
% 8.08/8.29      (![X0 : $i]:
% 8.08/8.29         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 8.08/8.29          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 8.08/8.29      inference('sup-', [status(thm)], ['18', '19'])).
% 8.08/8.29  thf('21', plain,
% 8.08/8.29      (((((sk_B) = (k1_relat_1 @ sk_C_1))
% 8.08/8.29         | (r2_hidden @ 
% 8.08/8.29            (k4_tarski @ (sk_C @ sk_B @ sk_C_1) @ 
% 8.08/8.29             (sk_D_1 @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)) @ 
% 8.08/8.29            (k2_zfmisc_1 @ sk_B @ sk_A))))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['17', '20'])).
% 8.08/8.29  thf(l54_zfmisc_1, axiom,
% 8.08/8.29    (![A:$i,B:$i,C:$i,D:$i]:
% 8.08/8.29     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 8.08/8.29       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 8.08/8.29  thf('22', plain,
% 8.08/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.08/8.29         ((r2_hidden @ X0 @ X1)
% 8.08/8.29          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 8.08/8.29      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 8.08/8.29  thf('23', plain,
% 8.08/8.29      (((((sk_B) = (k1_relat_1 @ sk_C_1))
% 8.08/8.29         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.08/8.29  thf('24', plain,
% 8.08/8.29      (((((sk_B) = (k1_relat_1 @ sk_C_1))
% 8.08/8.29         | (r2_hidden @ 
% 8.08/8.29            (k4_tarski @ (sk_C @ sk_B @ sk_C_1) @ 
% 8.08/8.29             (sk_D_1 @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)) @ 
% 8.08/8.29            sk_C_1)))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['14', '16'])).
% 8.08/8.29  thf('25', plain,
% 8.08/8.29      (![X10 : $i, X13 : $i, X14 : $i]:
% 8.08/8.29         (((X13) = (k1_relat_1 @ X10))
% 8.08/8.29          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X13 @ X10) @ X14) @ X10)
% 8.08/8.29          | ~ (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 8.08/8.29      inference('cnf', [status(esa)], [d4_relat_1])).
% 8.08/8.29  thf('26', plain,
% 8.08/8.29      (((((sk_B) = (k1_relat_1 @ sk_C_1))
% 8.08/8.29         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 8.08/8.29         | ((sk_B) = (k1_relat_1 @ sk_C_1))))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['24', '25'])).
% 8.08/8.29  thf('27', plain,
% 8.08/8.29      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 8.08/8.29         | ((sk_B) = (k1_relat_1 @ sk_C_1))))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('simplify', [status(thm)], ['26'])).
% 8.08/8.29  thf('28', plain,
% 8.08/8.29      ((((sk_B) = (k1_relat_1 @ sk_C_1)))
% 8.08/8.29         <= ((![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('clc', [status(thm)], ['23', '27'])).
% 8.08/8.29  thf('29', plain,
% 8.08/8.29      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.08/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.08/8.29  thf(redefinition_k1_relset_1, axiom,
% 8.08/8.29    (![A:$i,B:$i,C:$i]:
% 8.08/8.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.08/8.29       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 8.08/8.29  thf('30', plain,
% 8.08/8.29      (![X15 : $i, X16 : $i, X17 : $i]:
% 8.08/8.29         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 8.08/8.29          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 8.08/8.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 8.08/8.29  thf('31', plain,
% 8.08/8.29      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 8.08/8.29      inference('sup-', [status(thm)], ['29', '30'])).
% 8.08/8.29  thf('32', plain,
% 8.08/8.29      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) != (sk_B)))
% 8.08/8.29         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 8.08/8.29      inference('split', [status(esa)], ['0'])).
% 8.08/8.29  thf('33', plain,
% 8.08/8.29      ((((k1_relat_1 @ sk_C_1) != (sk_B)))
% 8.08/8.29         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['31', '32'])).
% 8.08/8.29  thf('34', plain,
% 8.08/8.29      ((((sk_B) != (sk_B)))
% 8.08/8.29         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))) & 
% 8.08/8.29             (![X19 : $i]:
% 8.08/8.29                ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29                 | ~ (r2_hidden @ X19 @ sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['28', '33'])).
% 8.08/8.29  thf('35', plain,
% 8.08/8.29      (~
% 8.08/8.29       (![X19 : $i]:
% 8.08/8.29          ((r2_hidden @ (k4_tarski @ X19 @ (sk_E @ X19)) @ sk_C_1)
% 8.08/8.29           | ~ (r2_hidden @ X19 @ sk_B))) | 
% 8.08/8.29       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))),
% 8.08/8.29      inference('simplify', [status(thm)], ['34'])).
% 8.08/8.29  thf('36', plain,
% 8.08/8.29      (![X18 : $i]:
% 8.08/8.29         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) != (sk_B))
% 8.08/8.29          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X18) @ sk_C_1))),
% 8.08/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.08/8.29  thf('37', plain,
% 8.08/8.29      ((![X18 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X18) @ sk_C_1)) | 
% 8.08/8.29       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))),
% 8.08/8.29      inference('split', [status(esa)], ['36'])).
% 8.08/8.29  thf('38', plain,
% 8.08/8.29      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 8.08/8.29      inference('split', [status(esa)], ['0'])).
% 8.08/8.29  thf('39', plain,
% 8.08/8.29      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 8.08/8.29      inference('sup-', [status(thm)], ['29', '30'])).
% 8.08/8.29  thf('40', plain,
% 8.08/8.29      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))
% 8.08/8.29         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 8.08/8.29      inference('split', [status(esa)], ['2'])).
% 8.08/8.29  thf('41', plain,
% 8.08/8.29      ((((k1_relat_1 @ sk_C_1) = (sk_B)))
% 8.08/8.29         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 8.08/8.29      inference('sup+', [status(thm)], ['39', '40'])).
% 8.08/8.29  thf('42', plain,
% 8.08/8.29      (![X10 : $i, X12 : $i]:
% 8.08/8.29         ((r2_hidden @ (k4_tarski @ X12 @ (sk_D_1 @ X12 @ X10)) @ X10)
% 8.08/8.29          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X10)))),
% 8.08/8.29      inference('simplify', [status(thm)], ['15'])).
% 8.08/8.29  thf('43', plain,
% 8.08/8.29      ((![X0 : $i]:
% 8.08/8.29          (~ (r2_hidden @ X0 @ sk_B)
% 8.08/8.29           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_C_1)) @ sk_C_1)))
% 8.08/8.29         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['41', '42'])).
% 8.08/8.29  thf('44', plain,
% 8.08/8.29      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 8.08/8.29         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 8.08/8.29             (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 8.08/8.29      inference('sup-', [status(thm)], ['38', '43'])).
% 8.08/8.29  thf('45', plain,
% 8.08/8.29      ((![X18 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X18) @ sk_C_1))
% 8.08/8.29         <= ((![X18 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X18) @ sk_C_1)))),
% 8.08/8.29      inference('split', [status(esa)], ['36'])).
% 8.08/8.29  thf('46', plain,
% 8.08/8.29      (~ (![X18 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X18) @ sk_C_1)) | 
% 8.08/8.29       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))) | 
% 8.08/8.29       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 8.08/8.29      inference('sup-', [status(thm)], ['44', '45'])).
% 8.08/8.29  thf('47', plain, ($false),
% 8.08/8.29      inference('sat_resolution*', [status(thm)], ['1', '3', '35', '37', '46'])).
% 8.08/8.29  
% 8.08/8.29  % SZS output end Refutation
% 8.08/8.29  
% 8.08/8.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
