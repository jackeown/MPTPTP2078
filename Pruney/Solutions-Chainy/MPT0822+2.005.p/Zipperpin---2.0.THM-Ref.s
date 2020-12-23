%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4AihMqZeRD

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 130 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  612 (1358 expanded)
%              Number of equality atoms :   38 (  74 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X25: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
      | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X25: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X25 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['8','13'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('16',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ( r2_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X25: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X25 @ sk_B ) )
   <= ! [X25: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ( ( ( k2_relat_1 @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ) @ sk_C_2 ) )
   <= ! [X25: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k2_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k2_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( ( k2_relat_1 @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X25: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('25',plain,
    ( ( ( ( k2_relat_1 @ sk_C_2 )
        = sk_B )
      | ~ ( r2_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) )
   <= ! [X25: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ( r2_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
   <= ! [X25: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      & ! [X25: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
          | ~ ( r2_hidden @ X25 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,
    ( ~ ! [X25: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X25 ) @ X25 ) @ sk_C_2 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X24: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ! [X24: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('39',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 ) @ X13 ) @ X11 )
      | ( X12
       != ( k2_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('42',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X13 @ X11 ) @ X13 ) @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_2 ) @ X0 ) @ sk_C_2 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ! [X24: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 )
   <= ! [X24: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['35'])).

thf('46',plain,
    ( ~ ! [X24: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','34','36','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4AihMqZeRD
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 57 iterations in 0.025s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.51  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(t23_relset_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( ![D:$i]:
% 0.20/0.51           ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.51                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.20/0.51         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51          ( ( ![D:$i]:
% 0.20/0.51              ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.51                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.20/0.51            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t23_relset_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 0.20/0.51        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.20/0.51       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X25 : $i]:
% 0.20/0.51         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51          | ~ (r2_hidden @ X25 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((![X25 : $i]:
% 0.20/0.51          ((r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51           | ~ (r2_hidden @ X25 @ sk_B))) | 
% 0.20/0.51       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         ((v5_relat_1 @ X18 @ X20)
% 0.20/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('6', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(d19_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         (~ (v5_relat_1 @ X7 @ X8)
% 0.20/0.51          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.20/0.51          | ~ (v1_relat_1 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.20/0.51          | (v1_relat_1 @ X5)
% 0.20/0.51          | ~ (v1_relat_1 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf(fc6_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.51  thf('13', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '13'])).
% 0.20/0.51  thf(d8_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.51       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C_2) = (sk_B))
% 0.20/0.51        | (r2_xboole_0 @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf(t6_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.20/0.51          ( ![C:$i]:
% 0.20/0.51            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C_2) = (sk_B))
% 0.20/0.51        | (r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_2)) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((![X25 : $i]:
% 0.20/0.51          ((r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51           | ~ (r2_hidden @ X25 @ sk_B)))
% 0.20/0.51         <= ((![X25 : $i]:
% 0.20/0.51                ((r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((((k2_relat_1 @ sk_C_2) = (sk_B))
% 0.20/0.51         | (r2_hidden @ 
% 0.20/0.51            (k4_tarski @ (sk_E @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_2))) @ 
% 0.20/0.51             (sk_C @ sk_B @ (k2_relat_1 @ sk_C_2))) @ 
% 0.20/0.51            sk_C_2)))
% 0.20/0.51         <= ((![X25 : $i]:
% 0.20/0.51                ((r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf(d5_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.20/0.51          | (r2_hidden @ X10 @ X12)
% 0.20/0.51          | ((X12) != (k2_relat_1 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         ((r2_hidden @ X10 @ (k2_relat_1 @ X11))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (((((k2_relat_1 @ sk_C_2) = (sk_B))
% 0.20/0.51         | (r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_2)) @ 
% 0.20/0.51            (k2_relat_1 @ sk_C_2))))
% 0.20/0.51         <= ((![X25 : $i]:
% 0.20/0.51                ((r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_xboole_0 @ X3 @ X4) | ~ (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((((k2_relat_1 @ sk_C_2) = (sk_B))
% 0.20/0.51         | ~ (r2_xboole_0 @ (k2_relat_1 @ sk_C_2) @ sk_B)))
% 0.20/0.51         <= ((![X25 : $i]:
% 0.20/0.51                ((r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C_2) = (sk_B))
% 0.20/0.51        | (r2_xboole_0 @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C_2) = (sk_B)))
% 0.20/0.51         <= ((![X25 : $i]:
% 0.20/0.51                ((r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.51      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.20/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B)))
% 0.20/0.51         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C_2) != (sk_B)))
% 0.20/0.51         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((((sk_B) != (sk_B)))
% 0.20/0.51         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 0.20/0.51             (![X25 : $i]:
% 0.20/0.51                ((r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (~
% 0.20/0.51       (![X25 : $i]:
% 0.20/0.51          ((r2_hidden @ (k4_tarski @ (sk_E @ X25) @ X25) @ sk_C_2)
% 0.20/0.51           | ~ (r2_hidden @ X25 @ sk_B))) | 
% 0.20/0.51       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X24 : $i]:
% 0.20/0.51         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((![X24 : $i]: ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2)) | 
% 0.20/0.51       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C_2) = (sk_B)))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X13 @ X12)
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X13 @ X11) @ X13) @ X11)
% 0.20/0.51          | ((X12) != (k2_relat_1 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X11 : $i, X13 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X13 @ X11) @ X13) @ X11)
% 0.20/0.51          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X11)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.51           | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_C_2) @ X0) @ sk_C_2)))
% 0.20/0.51         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 0.20/0.51         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.20/0.51             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((![X24 : $i]: ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2))
% 0.20/0.51         <= ((![X24 : $i]: ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2)))),
% 0.20/0.51      inference('split', [status(esa)], ['35'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (~ (![X24 : $i]: ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2)) | 
% 0.20/0.51       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.51  thf('47', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '3', '34', '36', '46'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
