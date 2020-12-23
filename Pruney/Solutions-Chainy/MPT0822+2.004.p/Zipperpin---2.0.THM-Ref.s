%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxco8Tz58q

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:58 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 179 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  836 (2076 expanded)
%              Number of equality atoms :   41 (  94 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X24: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
      | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
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
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X10 ) @ ( sk_C_1 @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k2_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,
    ( ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) ) @ sk_C_2 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ X0 ) )
        | ( sk_B
          = ( k2_relat_1 @ X0 ) )
        | ( r2_hidden @ ( sk_C_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,
    ( ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_C_2 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_C_1 @ X13 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('37',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('40',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      & ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ~ ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
          | ~ ( r2_hidden @ X24 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X23: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('52',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ( X11
       != ( k2_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('55',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_2 ) @ X0 ) @ sk_C_2 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,
    ( ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 )
   <= ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['48'])).

thf('59',plain,
    ( ~ ! [X23: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','47','49','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxco8Tz58q
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.18/1.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.40  % Solved by: fo/fo7.sh
% 1.18/1.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.40  % done 102 iterations in 0.927s
% 1.18/1.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.40  % SZS output start Refutation
% 1.18/1.40  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.18/1.40  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.40  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.18/1.40  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.18/1.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.18/1.40  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.18/1.40  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.18/1.40  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.18/1.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.18/1.40  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.18/1.40  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.18/1.40  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.18/1.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.40  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.18/1.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.40  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.18/1.40  thf(sk_E_type, type, sk_E: $i > $i).
% 1.18/1.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.40  thf(t23_relset_1, conjecture,
% 1.18/1.40    (![A:$i,B:$i,C:$i]:
% 1.18/1.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.40       ( ( ![D:$i]:
% 1.18/1.40           ( ~( ( r2_hidden @ D @ B ) & 
% 1.18/1.40                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 1.18/1.40         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 1.18/1.40  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.40    (~( ![A:$i,B:$i,C:$i]:
% 1.18/1.40        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.40          ( ( ![D:$i]:
% 1.18/1.40              ( ~( ( r2_hidden @ D @ B ) & 
% 1.18/1.40                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 1.18/1.40            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 1.18/1.40    inference('cnf.neg', [status(esa)], [t23_relset_1])).
% 1.18/1.40  thf('0', plain,
% 1.18/1.40      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 1.18/1.40        | (r2_hidden @ sk_D_2 @ sk_B))),
% 1.18/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.40  thf('1', plain,
% 1.18/1.40      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 1.18/1.40       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 1.18/1.40      inference('split', [status(esa)], ['0'])).
% 1.18/1.40  thf('2', plain,
% 1.18/1.40      (![X24 : $i]:
% 1.18/1.40         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))
% 1.18/1.40          | (r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40          | ~ (r2_hidden @ X24 @ sk_B))),
% 1.18/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.40  thf('3', plain,
% 1.18/1.40      ((![X24 : $i]:
% 1.18/1.40          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40           | ~ (r2_hidden @ X24 @ sk_B))) | 
% 1.18/1.40       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 1.18/1.40      inference('split', [status(esa)], ['2'])).
% 1.18/1.40  thf(d5_relat_1, axiom,
% 1.18/1.40    (![A:$i,B:$i]:
% 1.18/1.40     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.18/1.40       ( ![C:$i]:
% 1.18/1.40         ( ( r2_hidden @ C @ B ) <=>
% 1.18/1.40           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.18/1.40  thf('4', plain,
% 1.18/1.40      (![X10 : $i, X13 : $i]:
% 1.18/1.40         (((X13) = (k2_relat_1 @ X10))
% 1.18/1.40          | (r2_hidden @ 
% 1.18/1.40             (k4_tarski @ (sk_D @ X13 @ X10) @ (sk_C_1 @ X13 @ X10)) @ X10)
% 1.18/1.40          | (r2_hidden @ (sk_C_1 @ X13 @ X10) @ X13))),
% 1.18/1.40      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.18/1.40  thf('5', plain,
% 1.18/1.40      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.18/1.40         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 1.18/1.40          | (r2_hidden @ X9 @ X11)
% 1.18/1.40          | ((X11) != (k2_relat_1 @ X10)))),
% 1.18/1.40      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.18/1.40  thf('6', plain,
% 1.18/1.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.18/1.40         ((r2_hidden @ X9 @ (k2_relat_1 @ X10))
% 1.18/1.40          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 1.18/1.40      inference('simplify', [status(thm)], ['5'])).
% 1.18/1.40  thf('7', plain,
% 1.18/1.40      (![X0 : $i, X1 : $i]:
% 1.18/1.40         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 1.18/1.40          | ((X1) = (k2_relat_1 @ X0))
% 1.18/1.40          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.18/1.40      inference('sup-', [status(thm)], ['4', '6'])).
% 1.18/1.40  thf(d3_tarski, axiom,
% 1.18/1.40    (![A:$i,B:$i]:
% 1.18/1.40     ( ( r1_tarski @ A @ B ) <=>
% 1.18/1.40       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.18/1.40  thf('8', plain,
% 1.18/1.40      (![X1 : $i, X3 : $i]:
% 1.18/1.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.18/1.40      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.40  thf('9', plain,
% 1.18/1.40      ((![X24 : $i]:
% 1.18/1.40          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40           | ~ (r2_hidden @ X24 @ sk_B)))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('split', [status(esa)], ['2'])).
% 1.18/1.40  thf('10', plain,
% 1.18/1.40      ((![X0 : $i]:
% 1.18/1.40          ((r1_tarski @ sk_B @ X0)
% 1.18/1.40           | (r2_hidden @ 
% 1.18/1.40              (k4_tarski @ (sk_E @ (sk_C @ X0 @ sk_B)) @ (sk_C @ X0 @ sk_B)) @ 
% 1.18/1.40              sk_C_2)))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['8', '9'])).
% 1.18/1.40  thf('11', plain,
% 1.18/1.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.18/1.40         ((r2_hidden @ X9 @ (k2_relat_1 @ X10))
% 1.18/1.40          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 1.18/1.40      inference('simplify', [status(thm)], ['5'])).
% 1.18/1.40  thf('12', plain,
% 1.18/1.40      ((![X0 : $i]:
% 1.18/1.40          ((r1_tarski @ sk_B @ X0)
% 1.18/1.40           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['10', '11'])).
% 1.18/1.40  thf('13', plain,
% 1.18/1.40      (![X1 : $i, X3 : $i]:
% 1.18/1.40         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.18/1.40      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.40  thf('14', plain,
% 1.18/1.40      ((((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 1.18/1.40         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['12', '13'])).
% 1.18/1.40  thf('15', plain,
% 1.18/1.40      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('simplify', [status(thm)], ['14'])).
% 1.18/1.40  thf('16', plain,
% 1.18/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.40         (~ (r2_hidden @ X0 @ X1)
% 1.18/1.40          | (r2_hidden @ X0 @ X2)
% 1.18/1.40          | ~ (r1_tarski @ X1 @ X2))),
% 1.18/1.40      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.40  thf('17', plain,
% 1.18/1.40      ((![X0 : $i]:
% 1.18/1.40          ((r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)) | ~ (r2_hidden @ X0 @ sk_B)))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['15', '16'])).
% 1.18/1.40  thf('18', plain,
% 1.18/1.40      ((![X0 : $i]:
% 1.18/1.40          ((r2_hidden @ (sk_C_1 @ sk_B @ X0) @ (k2_relat_1 @ X0))
% 1.18/1.40           | ((sk_B) = (k2_relat_1 @ X0))
% 1.18/1.40           | (r2_hidden @ (sk_C_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_C_2))))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['7', '17'])).
% 1.18/1.40  thf('19', plain,
% 1.18/1.40      ((((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ (k2_relat_1 @ sk_C_2))
% 1.18/1.40         | ((sk_B) = (k2_relat_1 @ sk_C_2))))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('eq_fact', [status(thm)], ['18'])).
% 1.18/1.40  thf('20', plain,
% 1.18/1.40      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.40  thf(cc2_relset_1, axiom,
% 1.18/1.40    (![A:$i,B:$i,C:$i]:
% 1.18/1.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.40       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.18/1.40  thf('21', plain,
% 1.18/1.40      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.18/1.40         ((v5_relat_1 @ X17 @ X19)
% 1.18/1.40          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.18/1.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.18/1.40  thf('22', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 1.18/1.40      inference('sup-', [status(thm)], ['20', '21'])).
% 1.18/1.40  thf(d19_relat_1, axiom,
% 1.18/1.40    (![A:$i,B:$i]:
% 1.18/1.40     ( ( v1_relat_1 @ B ) =>
% 1.18/1.40       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.18/1.40  thf('23', plain,
% 1.18/1.40      (![X6 : $i, X7 : $i]:
% 1.18/1.40         (~ (v5_relat_1 @ X6 @ X7)
% 1.18/1.40          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 1.18/1.40          | ~ (v1_relat_1 @ X6))),
% 1.18/1.40      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.18/1.40  thf('24', plain,
% 1.18/1.40      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 1.18/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.18/1.40  thf('25', plain,
% 1.18/1.40      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.40  thf(cc2_relat_1, axiom,
% 1.18/1.40    (![A:$i]:
% 1.18/1.40     ( ( v1_relat_1 @ A ) =>
% 1.18/1.40       ( ![B:$i]:
% 1.18/1.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.18/1.40  thf('26', plain,
% 1.18/1.40      (![X4 : $i, X5 : $i]:
% 1.18/1.40         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.18/1.40          | (v1_relat_1 @ X4)
% 1.18/1.40          | ~ (v1_relat_1 @ X5))),
% 1.18/1.40      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.18/1.40  thf('27', plain,
% 1.18/1.40      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 1.18/1.40      inference('sup-', [status(thm)], ['25', '26'])).
% 1.18/1.40  thf(fc6_relat_1, axiom,
% 1.18/1.40    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.18/1.40  thf('28', plain,
% 1.18/1.40      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.18/1.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.18/1.40  thf('29', plain, ((v1_relat_1 @ sk_C_2)),
% 1.18/1.40      inference('demod', [status(thm)], ['27', '28'])).
% 1.18/1.40  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 1.18/1.40      inference('demod', [status(thm)], ['24', '29'])).
% 1.18/1.40  thf('31', plain,
% 1.18/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.40         (~ (r2_hidden @ X0 @ X1)
% 1.18/1.40          | (r2_hidden @ X0 @ X2)
% 1.18/1.40          | ~ (r1_tarski @ X1 @ X2))),
% 1.18/1.40      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.40  thf('32', plain,
% 1.18/1.40      (![X0 : $i]:
% 1.18/1.40         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 1.18/1.40      inference('sup-', [status(thm)], ['30', '31'])).
% 1.18/1.40  thf('33', plain,
% 1.18/1.40      (((((sk_B) = (k2_relat_1 @ sk_C_2))
% 1.18/1.40         | (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['19', '32'])).
% 1.18/1.40  thf('34', plain,
% 1.18/1.40      ((![X24 : $i]:
% 1.18/1.40          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40           | ~ (r2_hidden @ X24 @ sk_B)))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('split', [status(esa)], ['2'])).
% 1.18/1.40  thf('35', plain,
% 1.18/1.40      (((((sk_B) = (k2_relat_1 @ sk_C_2))
% 1.18/1.40         | (r2_hidden @ 
% 1.18/1.40            (k4_tarski @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 1.18/1.40             (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 1.18/1.40            sk_C_2)))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['33', '34'])).
% 1.18/1.40  thf('36', plain,
% 1.18/1.40      (![X10 : $i, X13 : $i, X14 : $i]:
% 1.18/1.40         (((X13) = (k2_relat_1 @ X10))
% 1.18/1.40          | ~ (r2_hidden @ (k4_tarski @ X14 @ (sk_C_1 @ X13 @ X10)) @ X10)
% 1.18/1.40          | ~ (r2_hidden @ (sk_C_1 @ X13 @ X10) @ X13))),
% 1.18/1.40      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.18/1.40  thf('37', plain,
% 1.18/1.40      (((((sk_B) = (k2_relat_1 @ sk_C_2))
% 1.18/1.40         | ~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 1.18/1.40         | ((sk_B) = (k2_relat_1 @ sk_C_2))))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['35', '36'])).
% 1.18/1.40  thf('38', plain,
% 1.18/1.40      (((~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 1.18/1.40         | ((sk_B) = (k2_relat_1 @ sk_C_2))))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('simplify', [status(thm)], ['37'])).
% 1.18/1.40  thf('39', plain,
% 1.18/1.40      (((((sk_B) = (k2_relat_1 @ sk_C_2))
% 1.18/1.40         | (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['19', '32'])).
% 1.18/1.40  thf('40', plain,
% 1.18/1.40      ((((sk_B) = (k2_relat_1 @ sk_C_2)))
% 1.18/1.40         <= ((![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('clc', [status(thm)], ['38', '39'])).
% 1.18/1.40  thf('41', plain,
% 1.18/1.40      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.40  thf(redefinition_k2_relset_1, axiom,
% 1.18/1.40    (![A:$i,B:$i,C:$i]:
% 1.18/1.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.40       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.18/1.40  thf('42', plain,
% 1.18/1.40      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.40         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.18/1.40          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.18/1.40      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.18/1.40  thf('43', plain,
% 1.18/1.40      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 1.18/1.40      inference('sup-', [status(thm)], ['41', '42'])).
% 1.18/1.40  thf('44', plain,
% 1.18/1.40      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B)))
% 1.18/1.40         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.18/1.40      inference('split', [status(esa)], ['0'])).
% 1.18/1.40  thf('45', plain,
% 1.18/1.40      ((((k2_relat_1 @ sk_C_2) != (sk_B)))
% 1.18/1.40         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['43', '44'])).
% 1.18/1.40  thf('46', plain,
% 1.18/1.40      ((((sk_B) != (sk_B)))
% 1.18/1.40         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 1.18/1.40             (![X24 : $i]:
% 1.18/1.40                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['40', '45'])).
% 1.18/1.40  thf('47', plain,
% 1.18/1.40      (~
% 1.18/1.40       (![X24 : $i]:
% 1.18/1.40          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.18/1.40           | ~ (r2_hidden @ X24 @ sk_B))) | 
% 1.18/1.40       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 1.18/1.40      inference('simplify', [status(thm)], ['46'])).
% 1.18/1.40  thf('48', plain,
% 1.18/1.40      (![X23 : $i]:
% 1.18/1.40         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 1.18/1.40          | ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2))),
% 1.18/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.40  thf('49', plain,
% 1.18/1.40      ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2)) | 
% 1.18/1.40       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 1.18/1.40      inference('split', [status(esa)], ['48'])).
% 1.18/1.40  thf('50', plain,
% 1.18/1.40      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 1.18/1.40      inference('split', [status(esa)], ['0'])).
% 1.18/1.40  thf('51', plain,
% 1.18/1.40      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 1.18/1.40      inference('sup-', [status(thm)], ['41', '42'])).
% 1.18/1.40  thf('52', plain,
% 1.18/1.40      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))
% 1.18/1.40         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.18/1.40      inference('split', [status(esa)], ['2'])).
% 1.18/1.40  thf('53', plain,
% 1.18/1.40      ((((k2_relat_1 @ sk_C_2) = (sk_B)))
% 1.18/1.40         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.18/1.40      inference('sup+', [status(thm)], ['51', '52'])).
% 1.18/1.40  thf('54', plain,
% 1.18/1.40      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.18/1.40         (~ (r2_hidden @ X12 @ X11)
% 1.18/1.40          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X12 @ X10) @ X12) @ X10)
% 1.18/1.40          | ((X11) != (k2_relat_1 @ X10)))),
% 1.18/1.40      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.18/1.40  thf('55', plain,
% 1.18/1.40      (![X10 : $i, X12 : $i]:
% 1.18/1.40         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X12 @ X10) @ X12) @ X10)
% 1.18/1.40          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X10)))),
% 1.18/1.40      inference('simplify', [status(thm)], ['54'])).
% 1.18/1.40  thf('56', plain,
% 1.18/1.40      ((![X0 : $i]:
% 1.18/1.40          (~ (r2_hidden @ X0 @ sk_B)
% 1.18/1.40           | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_C_2) @ X0) @ sk_C_2)))
% 1.18/1.40         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['53', '55'])).
% 1.18/1.40  thf('57', plain,
% 1.18/1.40      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 1.18/1.40         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 1.18/1.40             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.18/1.40      inference('sup-', [status(thm)], ['50', '56'])).
% 1.18/1.40  thf('58', plain,
% 1.18/1.40      ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2))
% 1.18/1.40         <= ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2)))),
% 1.18/1.40      inference('split', [status(esa)], ['48'])).
% 1.18/1.40  thf('59', plain,
% 1.18/1.40      (~ (![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2)) | 
% 1.18/1.40       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) | 
% 1.18/1.40       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 1.18/1.40      inference('sup-', [status(thm)], ['57', '58'])).
% 1.18/1.40  thf('60', plain, ($false),
% 1.18/1.40      inference('sat_resolution*', [status(thm)], ['1', '3', '47', '49', '59'])).
% 1.18/1.40  
% 1.18/1.40  % SZS output end Refutation
% 1.18/1.40  
% 1.18/1.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
