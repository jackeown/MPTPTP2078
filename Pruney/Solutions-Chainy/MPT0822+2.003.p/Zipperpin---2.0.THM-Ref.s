%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TzDtf49SYq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 157 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  804 (2060 expanded)
%              Number of equality atoms :   48 ( 114 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

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
    ! [X20: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5
        = ( k2_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X5 @ X2 ) @ ( sk_C @ X5 @ X2 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ ( k2_relat_1 @ X0 ) )
        | ( sk_B
          = ( k2_relat_1 @ X0 ) )
        | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ sk_B @ X0 ) ) @ ( sk_C @ sk_B @ X0 ) ) @ sk_C_1 ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_C @ X5 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('14',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('17',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ X0 ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k2_relat_1 @ sk_C_1 ) )
        | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ X0 ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','23'])).

thf('25',plain,
    ( ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ sk_B @ sk_C_1 ) ) @ ( sk_C @ sk_B @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X5
        = ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_C @ X5 @ X2 ) ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('28',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','23'])).

thf('31',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X20: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X20 @ sk_B ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
      & ! [X20: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X20 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ~ ! [X20: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X20 ) @ X20 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X20 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X19: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ sk_D_2 ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X19: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X19 @ sk_D_2 ) @ sk_C_1 )
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('46',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_1 ) @ X0 ) @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,
    ( ! [X19: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X19 @ sk_D_2 ) @ sk_C_1 )
   <= ! [X19: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X19 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['39'])).

thf('50',plain,
    ( ~ ! [X19: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X19 @ sk_D_2 ) @ sk_C_1 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','38','40','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TzDtf49SYq
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 62 iterations in 0.048s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.50  thf(t23_relset_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( ![D:$i]:
% 0.20/0.50           ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.50                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.20/0.50         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50          ( ( ![D:$i]:
% 0.20/0.50              ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.50                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.20/0.50            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t23_relset_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.20/0.50        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.20/0.50       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X20 : $i]:
% 0.20/0.50         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50          | ~ (r2_hidden @ X20 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((![X20 : $i]:
% 0.20/0.50          ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50           | ~ (r2_hidden @ X20 @ sk_B))) | 
% 0.20/0.50       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         ((v5_relat_1 @ X13 @ X15)
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('6', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(d5_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X2 : $i, X5 : $i]:
% 0.20/0.50         (((X5) = (k2_relat_1 @ X2))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ (sk_D @ X5 @ X2) @ (sk_C @ X5 @ X2)) @ X2)
% 0.20/0.50          | (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.20/0.50          | (r2_hidden @ X1 @ X3)
% 0.20/0.50          | ((X3) != (k2_relat_1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.20/0.50          | ((X1) = (k2_relat_1 @ X0))
% 0.20/0.50          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((![X20 : $i]:
% 0.20/0.50          ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50           | ~ (r2_hidden @ X20 @ sk_B)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((r2_hidden @ (sk_C @ sk_B @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.50           | ((sk_B) = (k2_relat_1 @ X0))
% 0.20/0.50           | (r2_hidden @ 
% 0.20/0.50              (k4_tarski @ (sk_E @ (sk_C @ sk_B @ X0)) @ (sk_C @ sk_B @ X0)) @ 
% 0.20/0.50              sk_C_1)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X2 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (((X5) = (k2_relat_1 @ X2))
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X6 @ (sk_C @ X5 @ X2)) @ X2)
% 0.20/0.50          | ~ (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.20/0.50         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 0.20/0.50         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.20/0.50         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.20/0.50         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 0.20/0.50         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.20/0.50          | ((X1) = (k2_relat_1 @ X0))
% 0.20/0.50          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.20/0.50         | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ (k2_relat_1 @ sk_C_1))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf(t202_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X7 @ (k2_relat_1 @ X8))
% 0.20/0.50          | (r2_hidden @ X7 @ X9)
% 0.20/0.50          | ~ (v5_relat_1 @ X8 @ X9)
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.20/0.50           | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.50           | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.20/0.50           | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ X0)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( v1_relat_1 @ C ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         ((v1_relat_1 @ X10)
% 0.20/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.50  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.20/0.50           | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.20/0.50           | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ X0)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.20/0.50         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((![X20 : $i]:
% 0.20/0.50          ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50           | ~ (r2_hidden @ X20 @ sk_B)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.20/0.50         | (r2_hidden @ 
% 0.20/0.50            (k4_tarski @ (sk_E @ (sk_C @ sk_B @ sk_C_1)) @ 
% 0.20/0.50             (sk_C @ sk_B @ sk_C_1)) @ 
% 0.20/0.50            sk_C_1)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X2 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (((X5) = (k2_relat_1 @ X2))
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X6 @ (sk_C @ X5 @ X2)) @ X2)
% 0.20/0.50          | ~ (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.20/0.50         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.20/0.50         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.20/0.50         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.20/0.50         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '23'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((((sk_B) = (k2_relat_1 @ sk_C_1)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B)))
% 0.20/0.50         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((((k2_relat_1 @ sk_C_1) != (sk_B)))
% 0.20/0.50         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((((sk_B) != (sk_B)))
% 0.20/0.50         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.20/0.50             (![X20 : $i]:
% 0.20/0.50                ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (~
% 0.20/0.50       (![X20 : $i]:
% 0.20/0.50          ((r2_hidden @ (k4_tarski @ (sk_E @ X20) @ X20) @ sk_C_1)
% 0.20/0.50           | ~ (r2_hidden @ X20 @ sk_B))) | 
% 0.20/0.50       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X19 : $i]:
% 0.20/0.50         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X19 @ sk_D_2) @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((![X19 : $i]: ~ (r2_hidden @ (k4_tarski @ X19 @ sk_D_2) @ sk_C_1)) | 
% 0.20/0.50       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))
% 0.20/0.50         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((((k2_relat_1 @ sk_C_1) = (sk_B)))
% 0.20/0.50         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.20/0.50          | ((X3) != (k2_relat_1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X2 : $i, X4 : $i]:
% 0.20/0.50         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.20/0.50          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.50           | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_C_1) @ X0) @ sk_C_1)))
% 0.20/0.50         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_D_2) @ sk_C_1))
% 0.20/0.50         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.20/0.50             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      ((![X19 : $i]: ~ (r2_hidden @ (k4_tarski @ X19 @ sk_D_2) @ sk_C_1))
% 0.20/0.50         <= ((![X19 : $i]: ~ (r2_hidden @ (k4_tarski @ X19 @ sk_D_2) @ sk_C_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['39'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (~ (![X19 : $i]: ~ (r2_hidden @ (k4_tarski @ X19 @ sk_D_2) @ sk_C_1)) | 
% 0.20/0.50       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 0.20/0.50       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain, ($false),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['1', '3', '38', '40', '50'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
