%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9if9sMYvEl

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:06 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 116 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  489 ( 975 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X28 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['9','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_2 ),
    inference(demod,[status(thm)],['20','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['14','31'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X16: $i] :
      ( ( ( k2_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('39',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

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

thf('40',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('41',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('47',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['4','39','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9if9sMYvEl
% 0.16/0.38  % Computer   : n025.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:48:51 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 117 iterations in 0.071s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(t49_relset_1, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56                    ( ![D:$i]:
% 0.38/0.56                      ( ( m1_subset_1 @ D @ B ) =>
% 0.38/0.56                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.56              ( ![C:$i]:
% 0.38/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56                       ( ![D:$i]:
% 0.38/0.56                         ( ( m1_subset_1 @ D @ B ) =>
% 0.38/0.56                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.38/0.56  thf('0', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.38/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('4', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.56  thf(existence_m1_subset_1, axiom,
% 0.38/0.56    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.38/0.56  thf('5', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.38/0.56      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.38/0.56  thf(t2_subset, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]:
% 0.38/0.56         ((r2_hidden @ X8 @ X9)
% 0.38/0.56          | (v1_xboole_0 @ X9)
% 0.38/0.56          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X28 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X28 @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 0.38/0.56          | ~ (m1_subset_1 @ X28 @ sk_B_2))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (((v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 0.38/0.56        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1)) @ 
% 0.38/0.56             sk_B_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.56         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.38/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.38/0.56        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_2))),
% 0.38/0.56      inference('demod', [status(thm)], ['9', '12', '13'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc2_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.56         ((v5_relat_1 @ X19 @ X21)
% 0.38/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.56  thf('18', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.56  thf(d19_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X12 : $i, X13 : $i]:
% 0.38/0.56         (~ (v5_relat_1 @ X12 @ X13)
% 0.38/0.56          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.38/0.56          | ~ (v1_relat_1 @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc2_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X10 : $i, X11 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.38/0.56          | (v1_relat_1 @ X10)
% 0.38/0.56          | ~ (v1_relat_1 @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf(fc6_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.56  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf('26', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2)),
% 0.38/0.56      inference('demod', [status(thm)], ['20', '25'])).
% 0.38/0.56  thf(d3_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.56          | (r2_hidden @ X0 @ X2)
% 0.38/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ X0 @ sk_B_2)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.38/0.56        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '28'])).
% 0.38/0.56  thf(t1_subset, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t1_subset])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.38/0.56        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.56  thf('32', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('clc', [status(thm)], ['14', '31'])).
% 0.38/0.56  thf(l13_xboole_0, axiom,
% 0.38/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.56  thf(t64_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.56           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.56         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X16 : $i]:
% 0.38/0.56         (((k2_relat_1 @ X16) != (k1_xboole_0))
% 0.38/0.56          | ((X16) = (k1_xboole_0))
% 0.38/0.56          | ~ (v1_relat_1 @ X16))),
% 0.38/0.56      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k2_relat_1 @ X1) != (X0))
% 0.38/0.56          | ~ (v1_xboole_0 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ((X1) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         (((X1) = (k1_xboole_0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_xboole_0 @ (k2_relat_1 @ X1)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.38/0.56  thf('37', plain, ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['32', '36'])).
% 0.38/0.56  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf('39', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf(s3_funct_1__e9_44_1__funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ?[B:$i]:
% 0.38/0.56       ( ( ![C:$i]:
% 0.38/0.56           ( ( r2_hidden @ C @ A ) =>
% 0.38/0.56             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.56         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.38/0.56         ( v1_relat_1 @ B ) ) ))).
% 0.38/0.56  thf('40', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B_1 @ X17)) = (X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (![X16 : $i]:
% 0.38/0.56         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.38/0.56          | ((X16) = (k1_xboole_0))
% 0.38/0.56          | ~ (v1_relat_1 @ X16))),
% 0.38/0.56      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((X0) != (k1_xboole_0))
% 0.38/0.56          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.38/0.56          | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.56  thf('43', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B_1 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.38/0.56  thf('45', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.56  thf('46', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B_1 @ X17)) = (X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.38/0.56  thf('47', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['45', '46'])).
% 0.38/0.56  thf('48', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '39', '47'])).
% 0.38/0.56  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
