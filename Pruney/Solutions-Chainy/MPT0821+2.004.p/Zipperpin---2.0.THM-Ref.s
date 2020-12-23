%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q0THFG5Lo6

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:56 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 121 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  634 (1262 expanded)
%              Number of equality atoms :   37 (  69 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X29: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
      | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
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
    ( ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ sk_C_2 ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X9 @ X12 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( sk_C_2
      = ( k7_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_C_2
    = ( k7_relat_1 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ! [X29: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
       != sk_B )
      & ! [X29: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
          | ~ ( r2_hidden @ X29 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ~ ! [X29: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_E @ X29 ) ) @ sk_C_2 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X28: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ! [X28: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_2 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('42',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('45',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ sk_C_2 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) ) @ sk_C_2 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,
    ( ! [X28: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_2 )
   <= ! [X28: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('49',plain,
    ( ~ ! [X28: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X28 ) @ sk_C_2 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','37','39','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q0THFG5Lo6
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 99 iterations in 0.066s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.52  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.34/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.52  thf(sk_E_type, type, sk_E: $i > $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.34/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.34/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.34/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.52  thf(t22_relset_1, conjecture,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.34/0.52       ( ( ![D:$i]:
% 0.34/0.52           ( ~( ( r2_hidden @ D @ B ) & 
% 0.34/0.52                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.34/0.52         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.34/0.52        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.34/0.52          ( ( ![D:$i]:
% 0.34/0.52              ( ~( ( r2_hidden @ D @ B ) & 
% 0.34/0.52                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.34/0.52            ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t22_relset_1])).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B))
% 0.34/0.52        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.34/0.52       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (![X29 : $i]:
% 0.34/0.52         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))
% 0.34/0.52          | (r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52          | ~ (r2_hidden @ X29 @ sk_B))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      ((![X29 : $i]:
% 0.34/0.52          ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.34/0.52       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['2'])).
% 0.34/0.52  thf(d3_tarski, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.34/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (![X1 : $i, X3 : $i]:
% 0.34/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      ((![X29 : $i]:
% 0.34/0.52          ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52           | ~ (r2_hidden @ X29 @ sk_B)))
% 0.34/0.52         <= ((![X29 : $i]:
% 0.34/0.52                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['2'])).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      ((![X0 : $i]:
% 0.34/0.52          ((r1_tarski @ sk_B @ X0)
% 0.34/0.52           | (r2_hidden @ 
% 0.34/0.52              (k4_tarski @ (sk_C @ X0 @ sk_B) @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.34/0.52              sk_C_2)))
% 0.34/0.52         <= ((![X29 : $i]:
% 0.34/0.52                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.34/0.52  thf(d4_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.34/0.52       ( ![C:$i]:
% 0.34/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.34/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.34/0.52         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.34/0.52          | (r2_hidden @ X9 @ X12)
% 0.34/0.52          | ((X12) != (k1_relat_1 @ X11)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.34/0.52         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 0.34/0.52          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.34/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      ((![X0 : $i]:
% 0.34/0.52          ((r1_tarski @ sk_B @ X0)
% 0.34/0.52           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_relat_1 @ sk_C_2))))
% 0.34/0.52         <= ((![X29 : $i]:
% 0.34/0.52                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['6', '8'])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X1 : $i, X3 : $i]:
% 0.34/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      ((((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))
% 0.34/0.52         | (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))))
% 0.34/0.52         <= ((![X29 : $i]:
% 0.34/0.52                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2)))
% 0.34/0.52         <= ((![X29 : $i]:
% 0.34/0.52                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(cc2_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.52         ((v4_relat_1 @ X22 @ X23)
% 0.34/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.34/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.52  thf('15', plain, ((v4_relat_1 @ sk_C_2 @ sk_B)),
% 0.34/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf(t209_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.34/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X18 : $i, X19 : $i]:
% 0.34/0.52         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.34/0.52          | ~ (v4_relat_1 @ X18 @ X19)
% 0.34/0.52          | ~ (v1_relat_1 @ X18))),
% 0.34/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      ((~ (v1_relat_1 @ sk_C_2) | ((sk_C_2) = (k7_relat_1 @ sk_C_2 @ sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(cc2_relat_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      (![X7 : $i, X8 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.34/0.52          | (v1_relat_1 @ X7)
% 0.34/0.52          | ~ (v1_relat_1 @ X8))),
% 0.34/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_2))),
% 0.34/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.34/0.52  thf(fc6_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.34/0.52  thf('21', plain,
% 0.34/0.52      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.34/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.34/0.52  thf('22', plain, ((v1_relat_1 @ sk_C_2)),
% 0.34/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.52  thf('23', plain, (((sk_C_2) = (k7_relat_1 @ sk_C_2 @ sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['17', '22'])).
% 0.34/0.52  thf(t87_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ B ) =>
% 0.34/0.52       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      (![X20 : $i, X21 : $i]:
% 0.34/0.52         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X20 @ X21)) @ X21)
% 0.34/0.52          | ~ (v1_relat_1 @ X20))),
% 0.34/0.52      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      (((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B) | ~ (v1_relat_1 @ sk_C_2))),
% 0.34/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.34/0.52  thf('26', plain, ((v1_relat_1 @ sk_C_2)),
% 0.34/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.52  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B)),
% 0.34/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.34/0.52  thf(d10_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (![X4 : $i, X6 : $i]:
% 0.34/0.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))
% 0.34/0.52        | ((sk_B) = (k1_relat_1 @ sk_C_2)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      ((((sk_B) = (k1_relat_1 @ sk_C_2)))
% 0.34/0.52         <= ((![X29 : $i]:
% 0.34/0.52                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['12', '29'])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.52         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.34/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.34/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.34/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B)))
% 0.34/0.52         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      ((((k1_relat_1 @ sk_C_2) != (sk_B)))
% 0.34/0.52         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      ((((sk_B) != (sk_B)))
% 0.34/0.52         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))) & 
% 0.34/0.52             (![X29 : $i]:
% 0.34/0.52                ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['30', '35'])).
% 0.34/0.52  thf('37', plain,
% 0.34/0.52      (~
% 0.34/0.52       (![X29 : $i]:
% 0.34/0.52          ((r2_hidden @ (k4_tarski @ X29 @ (sk_E @ X29)) @ sk_C_2)
% 0.34/0.52           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.34/0.52       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      (![X28 : $i]:
% 0.34/0.52         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B))
% 0.34/0.52          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_2))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('39', plain,
% 0.34/0.52      ((![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_2)) | 
% 0.34/0.52       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['38'])).
% 0.34/0.52  thf('40', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf('41', plain,
% 0.34/0.52      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.34/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.34/0.52  thf('42', plain,
% 0.34/0.52      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))
% 0.34/0.52         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['2'])).
% 0.34/0.52  thf('43', plain,
% 0.34/0.52      ((((k1_relat_1 @ sk_C_2) = (sk_B)))
% 0.34/0.52         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['41', '42'])).
% 0.34/0.52  thf('44', plain,
% 0.34/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X13 @ X12)
% 0.34/0.52          | (r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.34/0.52          | ((X12) != (k1_relat_1 @ X11)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.34/0.52  thf('45', plain,
% 0.34/0.52      (![X11 : $i, X13 : $i]:
% 0.34/0.52         ((r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.34/0.52          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.34/0.52  thf('46', plain,
% 0.34/0.52      ((![X0 : $i]:
% 0.34/0.52          (~ (r2_hidden @ X0 @ sk_B)
% 0.34/0.52           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_C_2)) @ sk_C_2)))
% 0.34/0.52         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['43', '45'])).
% 0.34/0.52  thf('47', plain,
% 0.34/0.52      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_2)) @ sk_C_2))
% 0.34/0.52         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.34/0.52             (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['40', '46'])).
% 0.34/0.52  thf('48', plain,
% 0.34/0.52      ((![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_2))
% 0.34/0.52         <= ((![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_2)))),
% 0.34/0.52      inference('split', [status(esa)], ['38'])).
% 0.34/0.52  thf('49', plain,
% 0.34/0.52      (~ (![X28 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X28) @ sk_C_2)) | 
% 0.34/0.52       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))) | 
% 0.34/0.52       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.34/0.52  thf('50', plain, ($false),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['1', '3', '37', '39', '49'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
