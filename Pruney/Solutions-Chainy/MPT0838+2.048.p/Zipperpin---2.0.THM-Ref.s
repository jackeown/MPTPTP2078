%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l5Rm0hYdVh

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 109 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  453 ( 827 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_D_1 @ X18 @ X16 ) ) @ X16 )
      | ( X17
       != ( k1_relat_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_D_1 @ X18 @ X16 ) ) @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','10'])).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('12',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_2 ),
    inference(demod,[status(thm)],['27','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X33: $i] :
      ~ ( r2_hidden @ X33 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['22','37'])).

thf('39',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('43',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('45',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.l5Rm0hYdVh
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 72 iterations in 0.030s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf(d4_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X18 @ X17)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X18 @ (sk_D_1 @ X18 @ X16)) @ X16)
% 0.20/0.49          | ((X17) != (k1_relat_1 @ X16)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X16 : $i, X18 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ X18 @ (sk_D_1 @ X18 @ X16)) @ X16)
% 0.20/0.49          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X16)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.20/0.49              (sk_D_1 @ (sk_B @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.20/0.49             X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(t7_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.49  thf('11', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '10'])).
% 0.20/0.49  thf(t49_relset_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49                    ( ![D:$i]:
% 0.20/0.49                      ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.49                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49                       ( ![D:$i]:
% 0.20/0.49                         ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.49                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.20/0.49  thf('12', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.49         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.20/0.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X33 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X33 @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 0.20/0.49          | ~ (m1_subset_1 @ X33 @ sk_B_2))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.49         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.20/0.49          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X33 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X33 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.49          | ~ (m1_subset_1 @ X33 @ sk_B_2))),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         ((v5_relat_1 @ X24 @ X26)
% 0.20/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('25', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf(d19_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (v5_relat_1 @ X12 @ X13)
% 0.20/0.49          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.49          | (v1_relat_1 @ X10)
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf(fc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2)),
% 0.20/0.49      inference('demod', [status(thm)], ['27', '32'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X4 : $i, X6 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf(t4_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.49          | (m1_subset_1 @ X7 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X0 @ sk_B_2)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain, (![X33 : $i]: ~ (r2_hidden @ X33 @ (k2_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('clc', [status(thm)], ['22', '37'])).
% 0.20/0.49  thf('39', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '38'])).
% 0.20/0.49  thf(fc9_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.49       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X23 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (k2_relat_1 @ X23))
% 0.20/0.49          | ~ (v1_relat_1 @ X23)
% 0.20/0.49          | (v1_xboole_0 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.20/0.49  thf('41', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('43', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('45', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf('46', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '45'])).
% 0.20/0.49  thf('47', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['11', '46'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
