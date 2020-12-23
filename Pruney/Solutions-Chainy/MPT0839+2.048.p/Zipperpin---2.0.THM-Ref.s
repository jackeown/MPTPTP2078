%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3owzLKKlhg

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:17 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 175 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  438 (1648 expanded)
%              Number of equality atoms :   27 (  75 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X19 ) @ ( sk_C_2 @ X19 ) ) @ X19 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X29 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X29 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_C_3 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C_3 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_C_3 = k1_xboole_0 ),
    inference(clc,[status(thm)],['16','31'])).

thf('33',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','32'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_C_3 = k1_xboole_0 ),
    inference(clc,[status(thm)],['16','31'])).

thf('40',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3owzLKKlhg
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 18:56:26 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.18/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.47  % Solved by: fo/fo7.sh
% 0.18/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.47  % done 87 iterations in 0.057s
% 0.18/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.47  % SZS output start Refutation
% 0.18/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.18/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.18/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.18/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.47  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.18/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.18/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.18/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.18/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.47  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.18/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.47  thf(t50_relset_1, conjecture,
% 0.18/0.47    (![A:$i]:
% 0.18/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.18/0.47       ( ![B:$i]:
% 0.18/0.47         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.18/0.47           ( ![C:$i]:
% 0.18/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.18/0.47               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.18/0.47                    ( ![D:$i]:
% 0.18/0.47                      ( ( m1_subset_1 @ D @ B ) =>
% 0.18/0.47                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.47    (~( ![A:$i]:
% 0.18/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.18/0.47          ( ![B:$i]:
% 0.18/0.47            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.18/0.47              ( ![C:$i]:
% 0.18/0.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.18/0.47                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.18/0.47                       ( ![D:$i]:
% 0.18/0.47                         ( ( m1_subset_1 @ D @ B ) =>
% 0.18/0.47                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.18/0.47    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.18/0.47  thf('0', plain,
% 0.18/0.47      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf(t56_relat_1, axiom,
% 0.18/0.47    (![A:$i]:
% 0.18/0.47     ( ( v1_relat_1 @ A ) =>
% 0.18/0.47       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.18/0.47         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.18/0.47  thf('1', plain,
% 0.18/0.47      (![X19 : $i]:
% 0.18/0.47         ((r2_hidden @ (k4_tarski @ (sk_B @ X19) @ (sk_C_2 @ X19)) @ X19)
% 0.18/0.47          | ((X19) = (k1_xboole_0))
% 0.18/0.47          | ~ (v1_relat_1 @ X19))),
% 0.18/0.47      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.18/0.47  thf(d4_relat_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.18/0.47       ( ![C:$i]:
% 0.18/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.18/0.47           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.18/0.47  thf('2', plain,
% 0.18/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.18/0.47         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.18/0.47          | (r2_hidden @ X10 @ X13)
% 0.18/0.47          | ((X13) != (k1_relat_1 @ X12)))),
% 0.18/0.47      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.18/0.47  thf('3', plain,
% 0.18/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.18/0.47         ((r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.18/0.47          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.18/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.18/0.47  thf('4', plain,
% 0.18/0.47      (![X0 : $i]:
% 0.18/0.47         (~ (v1_relat_1 @ X0)
% 0.18/0.47          | ((X0) = (k1_xboole_0))
% 0.18/0.47          | (r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['1', '3'])).
% 0.18/0.47  thf('5', plain,
% 0.18/0.47      (![X29 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X29 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3))
% 0.18/0.47          | ~ (m1_subset_1 @ X29 @ sk_B_1))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('6', plain,
% 0.18/0.47      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.18/0.47    (![A:$i,B:$i,C:$i]:
% 0.18/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.18/0.47  thf('7', plain,
% 0.18/0.47      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.18/0.47         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.18/0.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.18/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.18/0.47  thf('8', plain,
% 0.18/0.47      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.18/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.47  thf('9', plain,
% 0.18/0.47      (![X29 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X29 @ (k1_relat_1 @ sk_C_3))
% 0.18/0.47          | ~ (m1_subset_1 @ X29 @ sk_B_1))),
% 0.18/0.47      inference('demod', [status(thm)], ['5', '8'])).
% 0.18/0.47  thf('10', plain,
% 0.18/0.47      ((((sk_C_3) = (k1_xboole_0))
% 0.18/0.47        | ~ (v1_relat_1 @ sk_C_3)
% 0.18/0.47        | ~ (m1_subset_1 @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['4', '9'])).
% 0.18/0.47  thf('11', plain,
% 0.18/0.47      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf(cc2_relat_1, axiom,
% 0.18/0.47    (![A:$i]:
% 0.18/0.47     ( ( v1_relat_1 @ A ) =>
% 0.18/0.47       ( ![B:$i]:
% 0.18/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.18/0.47  thf('12', plain,
% 0.18/0.47      (![X6 : $i, X7 : $i]:
% 0.18/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.18/0.47          | (v1_relat_1 @ X6)
% 0.18/0.47          | ~ (v1_relat_1 @ X7))),
% 0.18/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.18/0.47  thf('13', plain,
% 0.18/0.47      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_C_3))),
% 0.18/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.18/0.47  thf(fc6_relat_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.18/0.47  thf('14', plain,
% 0.18/0.47      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.18/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.18/0.47  thf('15', plain, ((v1_relat_1 @ sk_C_3)),
% 0.18/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.18/0.47  thf('16', plain,
% 0.18/0.47      ((((sk_C_3) = (k1_xboole_0)) | ~ (m1_subset_1 @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.18/0.47      inference('demod', [status(thm)], ['10', '15'])).
% 0.18/0.47  thf('17', plain,
% 0.18/0.47      (![X0 : $i]:
% 0.18/0.47         (~ (v1_relat_1 @ X0)
% 0.18/0.47          | ((X0) = (k1_xboole_0))
% 0.18/0.47          | (r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['1', '3'])).
% 0.18/0.47  thf('18', plain,
% 0.18/0.47      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf(cc2_relset_1, axiom,
% 0.18/0.47    (![A:$i,B:$i,C:$i]:
% 0.18/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.18/0.47  thf('19', plain,
% 0.18/0.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.18/0.47         ((v4_relat_1 @ X20 @ X21)
% 0.18/0.47          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.18/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.18/0.47  thf('20', plain, ((v4_relat_1 @ sk_C_3 @ sk_B_1)),
% 0.18/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.18/0.47  thf(d18_relat_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( v1_relat_1 @ B ) =>
% 0.18/0.47       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.18/0.47  thf('21', plain,
% 0.18/0.47      (![X8 : $i, X9 : $i]:
% 0.18/0.47         (~ (v4_relat_1 @ X8 @ X9)
% 0.18/0.47          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.18/0.47          | ~ (v1_relat_1 @ X8))),
% 0.18/0.47      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.18/0.47  thf('22', plain,
% 0.18/0.47      ((~ (v1_relat_1 @ sk_C_3) | (r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B_1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.18/0.47  thf('23', plain, ((v1_relat_1 @ sk_C_3)),
% 0.18/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.18/0.47  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B_1)),
% 0.18/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.18/0.47  thf(d3_tarski, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.18/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.18/0.47  thf('25', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.18/0.47          | (r2_hidden @ X0 @ X2)
% 0.18/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.18/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.47  thf('26', plain,
% 0.18/0.47      (![X0 : $i]:
% 0.18/0.47         ((r2_hidden @ X0 @ sk_B_1)
% 0.18/0.47          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.18/0.47  thf('27', plain,
% 0.18/0.47      ((((sk_C_3) = (k1_xboole_0))
% 0.18/0.47        | ~ (v1_relat_1 @ sk_C_3)
% 0.18/0.47        | (r2_hidden @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['17', '26'])).
% 0.18/0.47  thf('28', plain, ((v1_relat_1 @ sk_C_3)),
% 0.18/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.18/0.47  thf('29', plain,
% 0.18/0.47      ((((sk_C_3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.18/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.18/0.47  thf(t1_subset, axiom,
% 0.18/0.47    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.18/0.47  thf('30', plain,
% 0.18/0.47      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.18/0.47      inference('cnf', [status(esa)], [t1_subset])).
% 0.18/0.47  thf('31', plain,
% 0.18/0.47      ((((sk_C_3) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.18/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.18/0.47  thf('32', plain, (((sk_C_3) = (k1_xboole_0))),
% 0.18/0.47      inference('clc', [status(thm)], ['16', '31'])).
% 0.18/0.47  thf('33', plain,
% 0.18/0.47      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.18/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.18/0.47      inference('demod', [status(thm)], ['0', '32'])).
% 0.18/0.47  thf(redefinition_k2_relset_1, axiom,
% 0.18/0.47    (![A:$i,B:$i,C:$i]:
% 0.18/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.18/0.47  thf('34', plain,
% 0.18/0.47      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.18/0.47         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.18/0.47          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.18/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.18/0.47  thf('35', plain,
% 0.18/0.47      (((k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0)
% 0.18/0.47         = (k2_relat_1 @ k1_xboole_0))),
% 0.18/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.18/0.47  thf(t60_relat_1, axiom,
% 0.18/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.18/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.18/0.47  thf('36', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.18/0.47  thf('37', plain,
% 0.18/0.47      (((k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.47      inference('demod', [status(thm)], ['35', '36'])).
% 0.18/0.47  thf('38', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) != (k1_xboole_0))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('39', plain, (((sk_C_3) = (k1_xboole_0))),
% 0.18/0.47      inference('clc', [status(thm)], ['16', '31'])).
% 0.18/0.47  thf('40', plain,
% 0.18/0.47      (((k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.18/0.47      inference('demod', [status(thm)], ['38', '39'])).
% 0.18/0.47  thf('41', plain, ($false),
% 0.18/0.47      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.18/0.47  
% 0.18/0.47  % SZS output end Refutation
% 0.18/0.47  
% 0.18/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
