%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xM3qBtE30G

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 101 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  442 ( 823 expanded)
%              Number of equality atoms :   35 (  54 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k1_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C ) )
      | ~ ( m1_subset_1 @ X28 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X28 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v5_relat_1 @ sk_C @ sk_B_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_2 ),
    inference(demod,[status(thm)],['15','20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X28: $i] :
      ~ ( r2_hidden @ X28 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['10','25'])).

thf('27',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X16: $i] :
      ( ( ( k2_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('34',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('35',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('36',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('42',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['4','34','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xM3qBtE30G
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 117 iterations in 0.076s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(t49_relset_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54                    ( ![D:$i]:
% 0.21/0.54                      ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.54                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54                       ( ![D:$i]:
% 0.21/0.54                         ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.54                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.21/0.54  thf('0', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.21/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('4', plain, (((k1_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.54  thf(d1_xboole_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X28 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X28 @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.21/0.54          | ~ (m1_subset_1 @ X28 @ sk_B_2))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.54         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.21/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X28 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X28 @ (k2_relat_1 @ sk_C))
% 0.21/0.54          | ~ (m1_subset_1 @ X28 @ sk_B_2))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '9'])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.54         ((v5_relat_1 @ X19 @ X21)
% 0.21/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.54  thf('13', plain, ((v5_relat_1 @ sk_C @ sk_B_2)),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf(d19_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i]:
% 0.21/0.54         (~ (v5_relat_1 @ X12 @ X13)
% 0.21/0.54          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.21/0.54          | ~ (v1_relat_1 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc2_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.21/0.54          | (v1_relat_1 @ X10)
% 0.21/0.54          | ~ (v1_relat_1 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_relat_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf(fc6_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.54  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_2)),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '20'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X4 : $i, X6 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf(t4_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.21/0.54          | (m1_subset_1 @ X7 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ sk_B_2)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain, (![X28 : $i]: ~ (r2_hidden @ X28 @ (k2_relat_1 @ sk_C))),
% 0.21/0.54      inference('clc', [status(thm)], ['10', '25'])).
% 0.21/0.54  thf('27', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '26'])).
% 0.21/0.54  thf(l13_xboole_0, axiom,
% 0.21/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.54  thf(t64_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X16 : $i]:
% 0.21/0.54         (((k2_relat_1 @ X16) != (k1_xboole_0))
% 0.21/0.54          | ((X16) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k2_relat_1 @ X1) != (X0))
% 0.21/0.54          | ~ (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | ((X1) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X1 : $i]:
% 0.21/0.54         (((X1) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_xboole_0 @ (k2_relat_1 @ X1)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.54  thf('32', plain, ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '31'])).
% 0.21/0.54  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('34', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf(s3_funct_1__e9_44_1__funct_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ?[B:$i]:
% 0.21/0.54       ( ( ![C:$i]:
% 0.21/0.54           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.54             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.54         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.54         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.54  thf('35', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B_1 @ X17)) = (X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X16 : $i]:
% 0.21/0.54         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.21/0.54          | ((X16) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((X0) != (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.21/0.54          | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B_1 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('40', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.54  thf('41', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B_1 @ X17)) = (X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.21/0.54  thf('42', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '34', '42'])).
% 0.21/0.54  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
