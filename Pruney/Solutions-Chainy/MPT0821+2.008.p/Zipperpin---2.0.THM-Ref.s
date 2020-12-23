%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U64EHot1z6

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:56 EST 2020

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

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X29: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
      | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B ) ),
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
    | ( r2_hidden @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('14',plain,(
    r2_hidden @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B ) ),
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
    r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B ),
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
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ sk_C_3 ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 )
      | ( r2_hidden @ X15 @ X18 )
      | ( X18
       != ( k1_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ ( k1_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_C_3 ) ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_3 ) )
      | ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_3 ) ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_3 ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
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
    ( ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B )
      | ( ( k1_relat_1 @ sk_C_3 )
        = sk_B ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
      = sk_B )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('31',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
       != sk_B )
      & ! [X29: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ! [X29: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X28: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ! [X28: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_3 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
     != sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('39',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_1 @ X19 @ X17 ) ) @ X17 )
      | ( X18
       != ( k1_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('42',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_1 @ X19 @ X17 ) ) @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_C_3 ) ) @ sk_C_3 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_3 ) ) @ sk_C_3 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ! [X28: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_3 )
   <= ! [X28: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_3 ) ),
    inference(split,[status(esa)],['35'])).

thf('46',plain,
    ( ~ ! [X28: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_3 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_3 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','34','36','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U64EHot1z6
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 124 iterations in 0.083s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.20/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.55  thf(t22_relset_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.55       ( ( ![D:$i]:
% 0.20/0.55           ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.55                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.20/0.55         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.55          ( ( ![D:$i]:
% 0.20/0.55              ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.55                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.20/0.55            ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t22_relset_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) != (sk_B))
% 0.20/0.55        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.20/0.55       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X29 : $i]:
% 0.20/0.55         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B))
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55          | ~ (r2_hidden @ X29 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      ((![X29 : $i]:
% 0.20/0.55          ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.20/0.55       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.55         ((m1_subset_1 @ (k1_relset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X22))
% 0.20/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_3) @ 
% 0.20/0.55        (k1_zfmisc_1 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.20/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((m1_subset_1 @ (k1_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.55  thf(t2_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         ((r2_hidden @ X13 @ X14)
% 0.20/0.55          | (v1_xboole_0 @ X14)
% 0.20/0.55          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.55        | (r2_hidden @ (k1_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf(fc1_subset_1, axiom,
% 0.20/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.55  thf('13', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((r2_hidden @ (k1_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.55      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf(d1_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.55          | (r1_tarski @ X10 @ X8)
% 0.20/0.55          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X8 : $i, X10 : $i]:
% 0.20/0.55         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.55  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B)),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.55  thf(d3_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X1 : $i, X3 : $i]:
% 0.20/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      ((![X29 : $i]:
% 0.20/0.55          ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55           | ~ (r2_hidden @ X29 @ sk_B)))
% 0.20/0.55         <= ((![X29 : $i]:
% 0.20/0.55                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((r1_tarski @ sk_B @ X0)
% 0.20/0.55           | (r2_hidden @ 
% 0.20/0.55              (k4_tarski @ (sk_C @ X0 @ sk_B) @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.20/0.55              sk_C_3)))
% 0.20/0.55         <= ((![X29 : $i]:
% 0.20/0.55                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf(d4_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.55       ( ![C:$i]:
% 0.20/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17)
% 0.20/0.55          | (r2_hidden @ X15 @ X18)
% 0.20/0.55          | ((X18) != (k1_relat_1 @ X17)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.55         ((r2_hidden @ X15 @ (k1_relat_1 @ X17))
% 0.20/0.55          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.20/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((r1_tarski @ sk_B @ X0)
% 0.20/0.55           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_relat_1 @ sk_C_3))))
% 0.20/0.55         <= ((![X29 : $i]:
% 0.20/0.55                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X1 : $i, X3 : $i]:
% 0.20/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_3))
% 0.20/0.55         | (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_3))))
% 0.20/0.55         <= ((![X29 : $i]:
% 0.20/0.55                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_3)))
% 0.20/0.55         <= ((![X29 : $i]:
% 0.20/0.55                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X4 : $i, X6 : $i]:
% 0.20/0.55         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (((~ (r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B)
% 0.20/0.55         | ((k1_relat_1 @ sk_C_3) = (sk_B))))
% 0.20/0.55         <= ((![X29 : $i]:
% 0.20/0.55                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((((k1_relat_1 @ sk_C_3) = (sk_B)))
% 0.20/0.55         <= ((![X29 : $i]:
% 0.20/0.55                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) != (sk_B)))
% 0.20/0.55         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      ((((k1_relat_1 @ sk_C_3) != (sk_B)))
% 0.20/0.55         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      ((((sk_B) != (sk_B)))
% 0.20/0.55         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B))) & 
% 0.20/0.55             (![X29 : $i]:
% 0.20/0.55                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (~
% 0.20/0.55       (![X29 : $i]:
% 0.20/0.55          ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_3)
% 0.20/0.55           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.20/0.55       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X28 : $i]:
% 0.20/0.55         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) != (sk_B))
% 0.20/0.55          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_3))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      ((![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_3)) | 
% 0.20/0.55       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B)))
% 0.20/0.55         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      ((((k1_relat_1 @ sk_C_3) = (sk_B)))
% 0.20/0.55         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X19 @ X18)
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X19 @ (sk_D_1 @ X19 @ X17)) @ X17)
% 0.20/0.55          | ((X18) != (k1_relat_1 @ X17)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X17 : $i, X19 : $i]:
% 0.20/0.55         ((r2_hidden @ (k4_tarski @ X19 @ (sk_D_1 @ X19 @ X17)) @ X17)
% 0.20/0.55          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X17)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.55           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_C_3)) @ sk_C_3)))
% 0.20/0.55         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_3)) @ sk_C_3))
% 0.20/0.55         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.20/0.55             (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['37', '43'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_3))
% 0.20/0.55         <= ((![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_3)))),
% 0.20/0.55      inference('split', [status(esa)], ['35'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (~ (![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_3)) | 
% 0.20/0.55       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_3) = (sk_B))) | 
% 0.20/0.55       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.55  thf('47', plain, ($false),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['1', '3', '34', '36', '46'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
