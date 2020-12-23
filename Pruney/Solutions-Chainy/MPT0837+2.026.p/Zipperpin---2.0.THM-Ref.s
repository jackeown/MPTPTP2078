%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qd59vrsxmL

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:58 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 147 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  642 (1715 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t48_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                <=> ? [E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                      & ( m1_subset_1 @ E @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X19 @ X17 ) @ X19 ) @ X17 )
      | ( X18
       != ( k2_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X19 @ X17 ) @ X19 ) @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('27',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 )
      | ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_B )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) )
      & ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
    | ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
    | ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X25 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ( X18
       != ( k2_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ ( k2_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['30','41','42','43','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qd59vrsxmL
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 181 iterations in 0.142s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.58  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.41/0.58  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.58  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.41/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.58  thf(t48_relset_1, conjecture,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.58           ( ![C:$i]:
% 0.41/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.58               ( ![D:$i]:
% 0.41/0.58                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.41/0.58                   ( ?[E:$i]:
% 0.41/0.58                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.41/0.58                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i]:
% 0.41/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.58          ( ![B:$i]:
% 0.41/0.58            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.58              ( ![C:$i]:
% 0.41/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.58                  ( ![D:$i]:
% 0.41/0.58                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.41/0.58                      ( ?[E:$i]:
% 0.41/0.58                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.41/0.58                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.58         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.41/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.41/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)
% 0.41/0.58        | (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))
% 0.41/0.58         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('split', [status(esa)], ['3'])).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (((r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_2)))
% 0.41/0.58         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('sup+', [status(thm)], ['2', '4'])).
% 0.41/0.58  thf(d5_relat_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.41/0.58       ( ![C:$i]:
% 0.41/0.58         ( ( r2_hidden @ C @ B ) <=>
% 0.41/0.58           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X19 @ X18)
% 0.41/0.58          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X19 @ X17) @ X19) @ X17)
% 0.41/0.58          | ((X18) != (k2_relat_1 @ X17)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      (![X17 : $i, X19 : $i]:
% 0.41/0.58         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X19 @ X17) @ X19) @ X17)
% 0.41/0.58          | ~ (r2_hidden @ X19 @ (k2_relat_1 @ X17)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['6'])).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 0.41/0.58         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['5', '7'])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(t3_subset, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      (![X9 : $i, X10 : $i]:
% 0.41/0.58         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.58  thf('11', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.58  thf(d3_tarski, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.58          | (r2_hidden @ X0 @ X2)
% 0.41/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 0.41/0.58          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.41/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ 
% 0.41/0.58         (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.41/0.58         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['8', '13'])).
% 0.41/0.58  thf(l54_zfmisc_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.58     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.41/0.58       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.41/0.58  thf('15', plain,
% 0.41/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.58         ((r2_hidden @ X4 @ X5)
% 0.41/0.58          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 0.41/0.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.41/0.58         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.58  thf('17', plain,
% 0.41/0.58      (![X1 : $i, X3 : $i]:
% 0.41/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      (![X1 : $i, X3 : $i]:
% 0.41/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.41/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.58  thf('19', plain,
% 0.41/0.58      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.58  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.41/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.41/0.58  thf('21', plain,
% 0.41/0.58      (![X9 : $i, X11 : $i]:
% 0.41/0.58         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.41/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.58  thf('22', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.58  thf(t4_subset, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.41/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X12 @ X13)
% 0.41/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.41/0.58          | (m1_subset_1 @ X12 @ X14))),
% 0.41/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.58  thf('25', plain,
% 0.41/0.58      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.41/0.58         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['16', '24'])).
% 0.41/0.58  thf('26', plain,
% 0.41/0.58      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 0.41/0.58         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['5', '7'])).
% 0.41/0.58  thf('27', plain,
% 0.41/0.58      (![X25 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58          | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2)
% 0.41/0.58          | ~ (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      ((![X25 : $i]:
% 0.41/0.58          (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58           | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2)))
% 0.41/0.58         <= ((![X25 : $i]:
% 0.41/0.58                (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58                 | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2))))),
% 0.41/0.58      inference('split', [status(esa)], ['27'])).
% 0.41/0.58  thf('29', plain,
% 0.41/0.58      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.41/0.58         <= ((![X25 : $i]:
% 0.41/0.58                (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58                 | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2))) & 
% 0.41/0.58             ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['26', '28'])).
% 0.41/0.58  thf('30', plain,
% 0.41/0.58      (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))) | 
% 0.41/0.58       ~
% 0.41/0.58       (![X25 : $i]:
% 0.41/0.58          (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58           | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['25', '29'])).
% 0.41/0.58  thf('31', plain,
% 0.41/0.58      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2))
% 0.41/0.58         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('split', [status(esa)], ['3'])).
% 0.41/0.58  thf('32', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 0.41/0.58          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.41/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.58  thf('33', plain,
% 0.41/0.58      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.41/0.58         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.58  thf('34', plain,
% 0.41/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.58         ((r2_hidden @ X4 @ X5)
% 0.41/0.58          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 0.41/0.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.41/0.58  thf('35', plain,
% 0.41/0.58      (((r2_hidden @ sk_E @ sk_B))
% 0.41/0.58         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.58  thf('37', plain,
% 0.41/0.58      (((m1_subset_1 @ sk_E @ sk_B))
% 0.41/0.58         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.58  thf('38', plain,
% 0.41/0.58      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2))
% 0.41/0.58         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('split', [status(esa)], ['3'])).
% 0.41/0.58  thf('39', plain,
% 0.41/0.58      ((![X25 : $i]:
% 0.41/0.58          (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58           | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2)))
% 0.41/0.58         <= ((![X25 : $i]:
% 0.41/0.58                (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58                 | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2))))),
% 0.41/0.58      inference('split', [status(esa)], ['27'])).
% 0.41/0.58  thf('40', plain,
% 0.41/0.58      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.41/0.58         <= ((![X25 : $i]:
% 0.41/0.58                (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58                 | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2))) & 
% 0.41/0.58             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.58  thf('41', plain,
% 0.41/0.58      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)) | 
% 0.41/0.58       ~
% 0.41/0.58       (![X25 : $i]:
% 0.41/0.58          (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58           | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['37', '40'])).
% 0.41/0.58  thf('42', plain,
% 0.41/0.58      (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))) | 
% 0.41/0.58       (![X25 : $i]:
% 0.41/0.58          (~ (m1_subset_1 @ X25 @ sk_B)
% 0.41/0.58           | ~ (r2_hidden @ (k4_tarski @ X25 @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('split', [status(esa)], ['27'])).
% 0.41/0.58  thf('43', plain,
% 0.41/0.58      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)) | 
% 0.41/0.58       ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.41/0.58      inference('split', [status(esa)], ['3'])).
% 0.41/0.58  thf('44', plain,
% 0.41/0.58      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2))
% 0.41/0.58         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('split', [status(esa)], ['3'])).
% 0.41/0.58  thf('45', plain,
% 0.41/0.58      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.58         (~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17)
% 0.41/0.58          | (r2_hidden @ X16 @ X18)
% 0.41/0.58          | ((X18) != (k2_relat_1 @ X17)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.41/0.58  thf('46', plain,
% 0.41/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.58         ((r2_hidden @ X16 @ (k2_relat_1 @ X17))
% 0.41/0.58          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.41/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.41/0.58  thf('47', plain,
% 0.41/0.58      (((r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_2)))
% 0.41/0.58         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['44', '46'])).
% 0.41/0.58  thf('48', plain,
% 0.41/0.58      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.41/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.58  thf('49', plain,
% 0.41/0.58      ((~ (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))
% 0.41/0.58         <= (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('split', [status(esa)], ['27'])).
% 0.41/0.58  thf('50', plain,
% 0.41/0.58      ((~ (r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_2)))
% 0.41/0.58         <= (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.58  thf('51', plain,
% 0.41/0.58      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)) | 
% 0.41/0.58       ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['47', '50'])).
% 0.41/0.58  thf('52', plain, ($false),
% 0.41/0.58      inference('sat_resolution*', [status(thm)],
% 0.41/0.58                ['30', '41', '42', '43', '51'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
