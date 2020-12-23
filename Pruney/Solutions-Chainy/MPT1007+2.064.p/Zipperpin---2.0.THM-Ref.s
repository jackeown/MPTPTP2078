%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yNTBSAxsVe

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 140 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  563 (1722 expanded)
%              Number of equality atoms :   34 (  96 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( X19 = k1_xboole_0 )
      | ( X19
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k1_funct_1 @ X18 @ X17 )
        = k1_xboole_0 )
      | ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X20 ) @ X18 )
      | ( X20
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( k1_funct_1 @ X18 @ X17 ) ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 = X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('23',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X30 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['22','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['32','35'])).

thf('39',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yNTBSAxsVe
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 102 iterations in 0.062s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(t61_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.52         ( m1_subset_1 @
% 0.21/0.52           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.52       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.52         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.52            ( m1_subset_1 @
% 0.21/0.52              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.52          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.52            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.21/0.52  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d4_funct_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52       ( ![B:$i,C:$i]:
% 0.21/0.52         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.52             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.52               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.52           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.52             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.52               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         ((r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.21/0.52          | ((X19) = (k1_xboole_0))
% 0.21/0.52          | ((X19) != (k1_funct_1 @ X18 @ X17))
% 0.21/0.52          | ~ (v1_funct_1 @ X18)
% 0.21/0.52          | ~ (v1_relat_1 @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X18)
% 0.21/0.52          | ~ (v1_funct_1 @ X18)
% 0.21/0.52          | ((k1_funct_1 @ X18 @ X17) = (k1_xboole_0))
% 0.21/0.52          | (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X17 @ X20) @ X18)
% 0.21/0.52          | ((X20) != (k1_funct_1 @ X18 @ X17))
% 0.21/0.52          | ~ (v1_funct_1 @ X18)
% 0.21/0.52          | ~ (v1_relat_1 @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X18)
% 0.21/0.52          | ~ (v1_funct_1 @ X18)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X17 @ (k1_funct_1 @ X18 @ X17)) @ X18)
% 0.21/0.52          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(l3_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X14 @ X15)
% 0.21/0.52          | (r2_hidden @ X14 @ X16)
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52          | ~ (v1_relat_1 @ sk_C)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.52  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( v1_relat_1 @ C ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         ((v1_relat_1 @ X21)
% 0.21/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.52  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '11', '14'])).
% 0.21/0.52  thf(t128_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( r2_hidden @
% 0.21/0.52         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.21/0.52       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         ((r2_hidden @ X9 @ X10)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ 
% 0.21/0.52               (k2_zfmisc_1 @ (k1_tarski @ X7) @ X10)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '11', '14'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         (((X8) = (X7))
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ 
% 0.21/0.52               (k2_zfmisc_1 @ (k1_tarski @ X7) @ X10)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0)) | ((X0) = (sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf(t6_mcart_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.52                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.21/0.52                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.21/0.52                       ( r2_hidden @ G @ B ) ) =>
% 0.21/0.52                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X24 : $i]:
% 0.21/0.52         (((X24) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X24) @ X24))),
% 0.21/0.52      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t7_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.52           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X30 @ X31)
% 0.21/0.52          | ((X32) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_funct_1 @ X33)
% 0.21/0.52          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.21/0.52          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ X33 @ X30) @ X32))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.21/0.52          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.52  thf('30', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.52        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.21/0.52           sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '31'])).
% 0.21/0.52  thf(t1_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.52  thf(t49_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k1_tarski @ X12) @ X13) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.52  thf('35', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ sk_B_1)),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['32', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.21/0.52        | ((sk_B @ (k1_tarski @ sk_A)) = (sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['22', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ sk_B_1)),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['32', '35'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)
% 0.21/0.52        | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.21/0.52      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain, ($false),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '19', '41'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
