%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dotSSYqSCg

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 109 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  632 (1216 expanded)
%              Number of equality atoms :   36 (  68 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X29: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
      | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k2_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('14',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_tarski @ X10 @ X8 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,
    ( ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) ) @ sk_C_3 ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ( X18
       != ( k2_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ ( k2_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_3 ) ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_3 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_3 ) ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_3 ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B )
      | ( ( k2_relat_1 @ sk_C_3 )
        = sk_B ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = sk_B )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('31',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
       != sk_B )
      & ! [X29: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ! [X29: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X29 ) @ X29 ) @ sk_C_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X28: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ! [X28: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_3 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
     != sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('39',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X19 @ X17 ) @ X19 ) @ X17 )
      | ( X18
       != ( k2_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('42',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X19 @ X17 ) @ X19 ) @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_3 ) @ X0 ) @ sk_C_3 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_3 ) @ sk_D_2 ) @ sk_C_3 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ! [X28: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_3 )
   <= ! [X28: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_3 ) ),
    inference(split,[status(esa)],['35'])).

thf('46',plain,
    ( ~ ! [X28: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_3 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','34','36','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dotSSYqSCg
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:13:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 124 iterations in 0.067s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(t23_relset_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( ![D:$i]:
% 0.20/0.52           ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.52                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.20/0.52         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52          ( ( ![D:$i]:
% 0.20/0.52              ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.52                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.20/0.52            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t23_relset_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) != (sk_B))
% 0.20/0.52        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.20/0.52       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X29 : $i]:
% 0.20/0.52         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52          | ~ (r2_hidden @ X29 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((![X29 : $i]:
% 0.20/0.52          ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.20/0.52       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k2_relset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X23))
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_3) @ 
% 0.20/0.52        (k1_zfmisc_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.52         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.20/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.52  thf(t2_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         ((r2_hidden @ X13 @ X14)
% 0.20/0.52          | (v1_xboole_0 @ X14)
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.52        | (r2_hidden @ (k2_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf(fc1_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('13', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((r2_hidden @ (k2_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf(d1_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.52          | (r1_tarski @ X10 @ X8)
% 0.20/0.52          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X8 : $i, X10 : $i]:
% 0.20/0.52         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.52  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((![X29 : $i]:
% 0.20/0.52          ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52           | ~ (r2_hidden @ X29 @ sk_B)))
% 0.20/0.52         <= ((![X29 : $i]:
% 0.20/0.52                ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r1_tarski @ sk_B @ X0)
% 0.20/0.52           | (r2_hidden @ 
% 0.20/0.52              (k4_tarski @ (sk_E @ (sk_C @ X0 @ sk_B)) @ (sk_C @ X0 @ sk_B)) @ 
% 0.20/0.52              sk_C_3)))
% 0.20/0.52         <= ((![X29 : $i]:
% 0.20/0.52                ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf(d5_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17)
% 0.20/0.52          | (r2_hidden @ X16 @ X18)
% 0.20/0.52          | ((X18) != (k2_relat_1 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         ((r2_hidden @ X16 @ (k2_relat_1 @ X17))
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.20/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r1_tarski @ sk_B @ X0)
% 0.20/0.52           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_3))))
% 0.20/0.52         <= ((![X29 : $i]:
% 0.20/0.52                ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_3))
% 0.20/0.52         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_3))))
% 0.20/0.52         <= ((![X29 : $i]:
% 0.20/0.52                ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_3)))
% 0.20/0.52         <= ((![X29 : $i]:
% 0.20/0.52                ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X4 : $i, X6 : $i]:
% 0.20/0.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((~ (r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B)
% 0.20/0.52         | ((k2_relat_1 @ sk_C_3) = (sk_B))))
% 0.20/0.52         <= ((![X29 : $i]:
% 0.20/0.52                ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((((k2_relat_1 @ sk_C_3) = (sk_B)))
% 0.20/0.52         <= ((![X29 : $i]:
% 0.20/0.52                ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) != (sk_B)))
% 0.20/0.52         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((((k2_relat_1 @ sk_C_3) != (sk_B)))
% 0.20/0.52         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((((sk_B) != (sk_B)))
% 0.20/0.52         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))) & 
% 0.20/0.52             (![X29 : $i]:
% 0.20/0.52                ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (~
% 0.20/0.52       (![X29 : $i]:
% 0.20/0.52          ((r2_hidden @ (k4_tarski @ (sk_E @ X29) @ X29) @ sk_C_3)
% 0.20/0.52           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.20/0.52       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X28 : $i]:
% 0.20/0.52         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) != (sk_B))
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_3))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_3)) | 
% 0.20/0.52       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B)))
% 0.20/0.52         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((((k2_relat_1 @ sk_C_3) = (sk_B)))
% 0.20/0.52         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X19 @ X18)
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X19 @ X17) @ X19) @ X17)
% 0.20/0.52          | ((X18) != (k2_relat_1 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X17 : $i, X19 : $i]:
% 0.20/0.52         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X19 @ X17) @ X19) @ X17)
% 0.20/0.52          | ~ (r2_hidden @ X19 @ (k2_relat_1 @ X17)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.52           | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_C_3) @ X0) @ sk_C_3)))
% 0.20/0.52         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_3) @ sk_D_2) @ sk_C_3))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.20/0.52             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_3))
% 0.20/0.52         <= ((![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_3)))),
% 0.20/0.52      inference('split', [status(esa)], ['35'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (~ (![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_3)) | 
% 0.20/0.52       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['1', '3', '34', '36', '46'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
