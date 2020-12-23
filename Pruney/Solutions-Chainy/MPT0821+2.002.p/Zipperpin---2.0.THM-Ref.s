%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wcCtjc06Hp

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:56 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 131 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  641 (1416 expanded)
%              Number of equality atoms :   40 (  79 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X28: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
      | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X28: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,
    ( ! [X28: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) )
   <= ! [X28: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ sk_C_2 ) )
   <= ! [X28: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k1_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ! [X28: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ! [X28: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
   <= ! [X28: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( sk_C_2
      = ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_C_2
    = ( k7_relat_1 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( sk_C_2
    = ( k7_relat_1 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ! [X28: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
       != sk_B )
      & ! [X28: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ~ ! [X28: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X28 @ ( sk_E @ X28 ) ) @ sk_C_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X27: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X27 ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ! [X27: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X27 ) @ sk_C_2 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('41',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( sk_D_1 @ X11 @ X9 ) ) @ X9 )
      | ( X10
       != ( k1_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('44',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ ( sk_D_1 @ X11 @ X9 ) ) @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ sk_C_2 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) ) @ sk_C_2 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ! [X27: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X27 ) @ sk_C_2 )
   <= ! [X27: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X27 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['37'])).

thf('48',plain,
    ( ~ ! [X27: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X27 ) @ sk_C_2 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','36','38','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wcCtjc06Hp
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 09:31:34 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 136 iterations in 0.157s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.61  thf(sk_E_type, type, sk_E: $i > $i).
% 0.41/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.41/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(t22_relset_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.61       ( ( ![D:$i]:
% 0.41/0.61           ( ~( ( r2_hidden @ D @ B ) & 
% 0.41/0.61                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.41/0.61         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.41/0.61          ( ( ![D:$i]:
% 0.41/0.61              ( ~( ( r2_hidden @ D @ B ) & 
% 0.41/0.61                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.41/0.61            ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t22_relset_1])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B))
% 0.41/0.61        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.41/0.61       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (![X28 : $i]:
% 0.41/0.61         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))
% 0.41/0.61          | (r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61          | ~ (r2_hidden @ X28 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      ((![X28 : $i]:
% 0.41/0.61          ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61           | ~ (r2_hidden @ X28 @ sk_B))) | 
% 0.41/0.61       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['2'])).
% 0.41/0.61  thf(d3_tarski, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      ((![X28 : $i]:
% 0.41/0.61          ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61           | ~ (r2_hidden @ X28 @ sk_B)))
% 0.41/0.61         <= ((![X28 : $i]:
% 0.41/0.61                ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.41/0.61      inference('split', [status(esa)], ['2'])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((r1_tarski @ sk_B @ X0)
% 0.41/0.61           | (r2_hidden @ 
% 0.41/0.61              (k4_tarski @ (sk_C @ X0 @ sk_B) @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.41/0.61              sk_C_2)))
% 0.41/0.61         <= ((![X28 : $i]:
% 0.41/0.61                ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf(d4_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.41/0.61       ( ![C:$i]:
% 0.41/0.61         ( ( r2_hidden @ C @ B ) <=>
% 0.41/0.61           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.61         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.41/0.61          | (r2_hidden @ X7 @ X10)
% 0.41/0.61          | ((X10) != (k1_relat_1 @ X9)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.61         ((r2_hidden @ X7 @ (k1_relat_1 @ X9))
% 0.41/0.61          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.41/0.61      inference('simplify', [status(thm)], ['7'])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((r1_tarski @ sk_B @ X0)
% 0.41/0.61           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_relat_1 @ sk_C_2))))
% 0.41/0.61         <= ((![X28 : $i]:
% 0.41/0.61                ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['6', '8'])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      ((((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))
% 0.41/0.61         | (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))))
% 0.41/0.61         <= ((![X28 : $i]:
% 0.41/0.61                ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2)))
% 0.41/0.61         <= ((![X28 : $i]:
% 0.41/0.61                ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.41/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(cc2_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.61         ((v4_relat_1 @ X21 @ X22)
% 0.41/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.61  thf('15', plain, ((v4_relat_1 @ sk_C_2 @ sk_B)),
% 0.41/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.61  thf(t209_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.41/0.61       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (![X14 : $i, X15 : $i]:
% 0.41/0.61         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.41/0.61          | ~ (v4_relat_1 @ X14 @ X15)
% 0.41/0.61          | ~ (v1_relat_1 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C_2) | ((sk_C_2) = (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(cc1_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( v1_relat_1 @ C ) ))).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         ((v1_relat_1 @ X18)
% 0.41/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.61  thf('20', plain, ((v1_relat_1 @ sk_C_2)),
% 0.41/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.61  thf('21', plain, (((sk_C_2) = (k7_relat_1 @ sk_C_2 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['17', '20'])).
% 0.41/0.61  thf(t87_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X16 : $i, X17 : $i]:
% 0.41/0.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X16 @ X17)) @ X17)
% 0.41/0.61          | ~ (v1_relat_1 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.41/0.61  thf(d10_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X4 : $i, X6 : $i]:
% 0.41/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X1)
% 0.41/0.61          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.41/0.61          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))
% 0.41/0.61        | ((sk_B) = (k1_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_B)))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C_2))),
% 0.41/0.61      inference('sup-', [status(thm)], ['21', '24'])).
% 0.41/0.61  thf('26', plain, (((sk_C_2) = (k7_relat_1 @ sk_C_2 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['17', '20'])).
% 0.41/0.61  thf('27', plain, ((v1_relat_1 @ sk_C_2)),
% 0.41/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))
% 0.41/0.61        | ((sk_B) = (k1_relat_1 @ sk_C_2)))),
% 0.41/0.61      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      ((((sk_B) = (k1_relat_1 @ sk_C_2)))
% 0.41/0.61         <= ((![X28 : $i]:
% 0.41/0.61                ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['12', '28'])).
% 0.41/0.61  thf('30', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.61         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.41/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.41/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B)))
% 0.41/0.61         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      ((((k1_relat_1 @ sk_C_2) != (sk_B)))
% 0.41/0.61         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      ((((sk_B) != (sk_B)))
% 0.41/0.61         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))) & 
% 0.41/0.61             (![X28 : $i]:
% 0.41/0.61                ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['29', '34'])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (~
% 0.41/0.61       (![X28 : $i]:
% 0.41/0.61          ((r2_hidden @ (k4_tarski @ X28 @ (sk_E @ X28)) @ sk_C_2)
% 0.41/0.61           | ~ (r2_hidden @ X28 @ sk_B))) | 
% 0.41/0.61       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['35'])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X27 : $i]:
% 0.41/0.61         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B))
% 0.41/0.61          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X27) @ sk_C_2))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      ((![X27 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X27) @ sk_C_2)) | 
% 0.41/0.61       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['37'])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.41/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))
% 0.41/0.61         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.41/0.61      inference('split', [status(esa)], ['2'])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      ((((k1_relat_1 @ sk_C_2) = (sk_B)))
% 0.41/0.61         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['40', '41'])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X11 @ X10)
% 0.41/0.61          | (r2_hidden @ (k4_tarski @ X11 @ (sk_D_1 @ X11 @ X9)) @ X9)
% 0.41/0.61          | ((X10) != (k1_relat_1 @ X9)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      (![X9 : $i, X11 : $i]:
% 0.41/0.61         ((r2_hidden @ (k4_tarski @ X11 @ (sk_D_1 @ X11 @ X9)) @ X9)
% 0.41/0.61          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X9)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          (~ (r2_hidden @ X0 @ sk_B)
% 0.41/0.61           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_C_2)) @ sk_C_2)))
% 0.41/0.61         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['42', '44'])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_2)) @ sk_C_2))
% 0.41/0.61         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.41/0.61             (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['39', '45'])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      ((![X27 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X27) @ sk_C_2))
% 0.41/0.61         <= ((![X27 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X27) @ sk_C_2)))),
% 0.41/0.61      inference('split', [status(esa)], ['37'])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      (~ (![X27 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X27) @ sk_C_2)) | 
% 0.41/0.61       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))) | 
% 0.41/0.61       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.61  thf('49', plain, ($false),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['1', '3', '36', '38', '48'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
