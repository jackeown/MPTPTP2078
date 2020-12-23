%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XT7dsqOFh7

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:58 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 209 expanded)
%              Number of leaves         :   28 (  72 expanded)
%              Depth                    :   23
%              Number of atoms          :  896 (2180 expanded)
%              Number of equality atoms :   40 (  86 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

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
    ! [X26: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
      | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) )
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
    ! [X9: $i,X12: $i] :
      ( ( X12
        = ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X9 ) @ ( sk_C_1 @ X12 @ X9 ) ) @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k2_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
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

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ( X10
       != ( k2_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('10',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_C_2 ) @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( v5_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['45'])).

thf('47',plain,
    ( ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_C_2 ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X9: $i,X12: $i,X13: $i] :
      ( ( X12
        = ( k2_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_C_1 @ X12 @ X9 ) ) @ X9 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('50',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['45'])).

thf('53',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      & ! [X26: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
          | ~ ( r2_hidden @ X26 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ~ ! [X26: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X26 ) @ X26 ) @ sk_C_2 )
          | ~ ( r2_hidden @ X26 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X25: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ! [X25: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('65',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_2 ) @ X0 ) @ sk_C_2 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ! [X25: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 )
   <= ! [X25: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['61'])).

thf('71',plain,
    ( ~ ! [X25: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','60','62','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XT7dsqOFh7
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:21:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 329 iterations in 0.237s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.45/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.69  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.45/0.69  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.45/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.69  thf(sk_E_type, type, sk_E: $i > $i).
% 0.45/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.45/0.69  thf(t23_relset_1, conjecture,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( ![D:$i]:
% 0.45/0.69           ( ~( ( r2_hidden @ D @ B ) & 
% 0.45/0.69                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.45/0.69         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.69        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69          ( ( ![D:$i]:
% 0.45/0.69              ( ~( ( r2_hidden @ D @ B ) & 
% 0.45/0.69                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.45/0.69            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t23_relset_1])).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 0.45/0.69        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.45/0.69       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.45/0.69      inference('split', [status(esa)], ['0'])).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (![X26 : $i]:
% 0.45/0.69         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))
% 0.45/0.69          | (r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69          | ~ (r2_hidden @ X26 @ sk_B))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      ((![X26 : $i]:
% 0.45/0.69          ((r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69           | ~ (r2_hidden @ X26 @ sk_B))) | 
% 0.45/0.69       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.45/0.69      inference('split', [status(esa)], ['2'])).
% 0.45/0.69  thf(d5_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.69       ( ![C:$i]:
% 0.45/0.69         ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.69           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (![X9 : $i, X12 : $i]:
% 0.45/0.69         (((X12) = (k2_relat_1 @ X9))
% 0.45/0.69          | (r2_hidden @ 
% 0.45/0.69             (k4_tarski @ (sk_D @ X12 @ X9) @ (sk_C_1 @ X12 @ X9)) @ X9)
% 0.45/0.69          | (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.45/0.69      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.69         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.45/0.69          | (r2_hidden @ X8 @ X10)
% 0.45/0.69          | ((X10) != (k2_relat_1 @ X9)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.69         ((r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 0.45/0.69          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.45/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.45/0.69          | ((X1) = (k2_relat_1 @ X0))
% 0.45/0.69          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['4', '6'])).
% 0.45/0.69  thf(d3_tarski, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X11 @ X10)
% 0.45/0.69          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X11 @ X9) @ X11) @ X9)
% 0.45/0.69          | ((X10) != (k2_relat_1 @ X9)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X9 : $i, X11 : $i]:
% 0.45/0.69         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X11 @ X9) @ X11) @ X9)
% 0.45/0.69          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X9)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.45/0.69          | (r2_hidden @ 
% 0.45/0.69             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.45/0.69              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 0.45/0.69             X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['8', '10'])).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(t3_subset, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X4 : $i, X5 : $i]:
% 0.45/0.69         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.69  thf('14', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.69          | (r2_hidden @ X0 @ X2)
% 0.45/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.45/0.69          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.45/0.69          | (r2_hidden @ 
% 0.45/0.69             (k4_tarski @ 
% 0.45/0.69              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_C_2) @ 
% 0.45/0.69              (sk_C @ X0 @ (k2_relat_1 @ sk_C_2))) @ 
% 0.45/0.69             (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['11', '16'])).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.69         ((r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 0.45/0.69          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.45/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.45/0.69          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ 
% 0.45/0.69             (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.69  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.45/0.69      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      (![X4 : $i, X6 : $i]:
% 0.45/0.69         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.69  thf('25', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.69  thf(cc2_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.69         ((v5_relat_1 @ X19 @ X21)
% 0.45/0.69          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 0.45/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf(t202_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.45/0.69       ( ![C:$i]:
% 0.45/0.69         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X16 @ (k2_relat_1 @ X17))
% 0.45/0.69          | (r2_hidden @ X16 @ X18)
% 0.45/0.69          | ~ (v5_relat_1 @ X17 @ X18)
% 0.45/0.69          | ~ (v1_relat_1 @ X17))),
% 0.45/0.69      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v5_relat_1 @ X0 @ X2)
% 0.45/0.69          | (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_C @ X2 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ 
% 0.45/0.69           X0)
% 0.45/0.69          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.45/0.69          | (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['27', '30'])).
% 0.45/0.69  thf(fc6_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_C @ X2 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ 
% 0.45/0.69           X0)
% 0.45/0.69          | (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2))),
% 0.45/0.69      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.69  thf('34', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 0.45/0.69          | (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)),
% 0.45/0.69      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.69          | (r2_hidden @ X0 @ X2)
% 0.45/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((r2_hidden @ X2 @ X0)
% 0.45/0.69          | ~ (r2_hidden @ X2 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.45/0.69          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['19', '38'])).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 0.45/0.69        | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.69  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.45/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.69          | (r2_hidden @ X0 @ X2)
% 0.45/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.69          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 0.45/0.69          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['7', '44'])).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      (((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 0.45/0.69        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.45/0.69      inference('eq_fact', [status(thm)], ['45'])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      ((![X26 : $i]:
% 0.45/0.69          ((r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69           | ~ (r2_hidden @ X26 @ sk_B)))
% 0.45/0.69         <= ((![X26 : $i]:
% 0.45/0.69                ((r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.45/0.69      inference('split', [status(esa)], ['2'])).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (((((sk_B) = (k2_relat_1 @ sk_C_2))
% 0.45/0.69         | (r2_hidden @ 
% 0.45/0.69            (k4_tarski @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 0.45/0.69             (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 0.45/0.69            sk_C_2)))
% 0.45/0.69         <= ((![X26 : $i]:
% 0.45/0.69                ((r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (![X9 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         (((X12) = (k2_relat_1 @ X9))
% 0.45/0.69          | ~ (r2_hidden @ (k4_tarski @ X13 @ (sk_C_1 @ X12 @ X9)) @ X9)
% 0.45/0.69          | ~ (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.45/0.69      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      (((((sk_B) = (k2_relat_1 @ sk_C_2))
% 0.45/0.69         | ~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 0.45/0.69         | ((sk_B) = (k2_relat_1 @ sk_C_2))))
% 0.45/0.69         <= ((![X26 : $i]:
% 0.45/0.69                ((r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.69  thf('51', plain,
% 0.45/0.69      (((~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 0.45/0.69         | ((sk_B) = (k2_relat_1 @ sk_C_2))))
% 0.45/0.69         <= ((![X26 : $i]:
% 0.45/0.69                ((r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.45/0.69      inference('simplify', [status(thm)], ['50'])).
% 0.45/0.69  thf('52', plain,
% 0.45/0.69      (((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 0.45/0.69        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.45/0.69      inference('eq_fact', [status(thm)], ['45'])).
% 0.45/0.69  thf('53', plain,
% 0.45/0.69      ((((sk_B) = (k2_relat_1 @ sk_C_2)))
% 0.45/0.69         <= ((![X26 : $i]:
% 0.45/0.69                ((r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.45/0.69      inference('clc', [status(thm)], ['51', '52'])).
% 0.45/0.69  thf('54', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.69  thf('55', plain,
% 0.45/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.69         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.45/0.69          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.69  thf('56', plain,
% 0.45/0.69      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B)))
% 0.45/0.69         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.45/0.69      inference('split', [status(esa)], ['0'])).
% 0.45/0.69  thf('58', plain,
% 0.45/0.69      ((((k2_relat_1 @ sk_C_2) != (sk_B)))
% 0.45/0.69         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      ((((sk_B) != (sk_B)))
% 0.45/0.69         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.45/0.69             (![X26 : $i]:
% 0.45/0.69                ((r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['53', '58'])).
% 0.45/0.69  thf('60', plain,
% 0.45/0.69      (~
% 0.45/0.69       (![X26 : $i]:
% 0.45/0.69          ((r2_hidden @ (k4_tarski @ (sk_E @ X26) @ X26) @ sk_C_2)
% 0.45/0.69           | ~ (r2_hidden @ X26 @ sk_B))) | 
% 0.45/0.69       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['59'])).
% 0.45/0.69  thf('61', plain,
% 0.45/0.69      (![X25 : $i]:
% 0.45/0.69         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 0.45/0.69          | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      ((![X25 : $i]: ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2)) | 
% 0.45/0.69       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.45/0.69      inference('split', [status(esa)], ['61'])).
% 0.45/0.69  thf('63', plain,
% 0.45/0.69      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.45/0.69      inference('split', [status(esa)], ['0'])).
% 0.45/0.69  thf('64', plain,
% 0.45/0.69      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))
% 0.45/0.69         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.45/0.69      inference('split', [status(esa)], ['2'])).
% 0.45/0.69  thf('66', plain,
% 0.45/0.69      ((((k2_relat_1 @ sk_C_2) = (sk_B)))
% 0.45/0.69         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['64', '65'])).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      (![X9 : $i, X11 : $i]:
% 0.45/0.69         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X11 @ X9) @ X11) @ X9)
% 0.45/0.69          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X9)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.69  thf('68', plain,
% 0.45/0.69      ((![X0 : $i]:
% 0.45/0.69          (~ (r2_hidden @ X0 @ sk_B)
% 0.45/0.69           | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_C_2) @ X0) @ sk_C_2)))
% 0.45/0.69         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.69  thf('69', plain,
% 0.45/0.69      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 0.45/0.69         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.45/0.69             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['63', '68'])).
% 0.45/0.69  thf('70', plain,
% 0.45/0.69      ((![X25 : $i]: ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2))
% 0.45/0.69         <= ((![X25 : $i]: ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2)))),
% 0.45/0.69      inference('split', [status(esa)], ['61'])).
% 0.45/0.69  thf('71', plain,
% 0.45/0.69      (~ (![X25 : $i]: ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2)) | 
% 0.45/0.69       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) | 
% 0.45/0.69       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.69  thf('72', plain, ($false),
% 0.45/0.69      inference('sat_resolution*', [status(thm)], ['1', '3', '60', '62', '71'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
