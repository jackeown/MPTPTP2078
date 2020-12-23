%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qwyyihe6Xs

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:20 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   81 (  96 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  555 ( 854 expanded)
%              Number of equality atoms :   31 (  43 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

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

thf('5',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ ( sk_D @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( sk_D @ X0 @ sk_C_2 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['10','28'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','31'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X27 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qwyyihe6Xs
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.30/1.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.30/1.48  % Solved by: fo/fo7.sh
% 1.30/1.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.48  % done 1029 iterations in 1.026s
% 1.30/1.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.30/1.48  % SZS output start Refutation
% 1.30/1.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.30/1.48  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.30/1.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.30/1.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.30/1.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.30/1.48  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.30/1.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.30/1.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.30/1.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.30/1.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.30/1.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.30/1.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.30/1.48  thf(sk_B_type, type, sk_B: $i).
% 1.30/1.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.30/1.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.30/1.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.30/1.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.30/1.48  thf('0', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 1.30/1.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.30/1.48  thf(d4_relat_1, axiom,
% 1.30/1.48    (![A:$i,B:$i]:
% 1.30/1.48     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.30/1.48       ( ![C:$i]:
% 1.30/1.48         ( ( r2_hidden @ C @ B ) <=>
% 1.30/1.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.30/1.48  thf('1', plain,
% 1.30/1.48      (![X20 : $i, X23 : $i]:
% 1.30/1.48         (((X23) = (k1_relat_1 @ X20))
% 1.30/1.48          | (r2_hidden @ 
% 1.30/1.48             (k4_tarski @ (sk_C_1 @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 1.30/1.48          | (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 1.30/1.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.30/1.48  thf('2', plain,
% 1.30/1.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.30/1.48         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 1.30/1.48          | (r2_hidden @ X18 @ X21)
% 1.30/1.48          | ((X21) != (k1_relat_1 @ X20)))),
% 1.30/1.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.30/1.48  thf('3', plain,
% 1.30/1.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.30/1.48         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 1.30/1.48          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 1.30/1.48      inference('simplify', [status(thm)], ['2'])).
% 1.30/1.48  thf('4', plain,
% 1.30/1.48      (![X0 : $i, X1 : $i]:
% 1.30/1.48         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 1.30/1.48          | ((X1) = (k1_relat_1 @ X0))
% 1.30/1.48          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.30/1.48      inference('sup-', [status(thm)], ['1', '3'])).
% 1.30/1.48  thf(t50_relset_1, conjecture,
% 1.30/1.48    (![A:$i]:
% 1.30/1.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.30/1.48       ( ![B:$i]:
% 1.30/1.48         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.30/1.48           ( ![C:$i]:
% 1.30/1.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.30/1.48               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 1.30/1.48                    ( ![D:$i]:
% 1.30/1.48                      ( ( m1_subset_1 @ D @ B ) =>
% 1.30/1.48                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.30/1.48  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.48    (~( ![A:$i]:
% 1.30/1.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.30/1.48          ( ![B:$i]:
% 1.30/1.48            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.30/1.48              ( ![C:$i]:
% 1.30/1.48                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.30/1.48                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 1.30/1.48                       ( ![D:$i]:
% 1.30/1.48                         ( ( m1_subset_1 @ D @ B ) =>
% 1.30/1.48                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.30/1.48    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 1.30/1.48  thf('5', plain,
% 1.30/1.48      (![X36 : $i]:
% 1.30/1.48         (~ (r2_hidden @ X36 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_2))
% 1.30/1.48          | ~ (m1_subset_1 @ X36 @ sk_B))),
% 1.30/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.48  thf('6', plain,
% 1.30/1.48      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.48  thf(redefinition_k1_relset_1, axiom,
% 1.30/1.48    (![A:$i,B:$i,C:$i]:
% 1.30/1.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.30/1.48  thf('7', plain,
% 1.30/1.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.30/1.48         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.30/1.48          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.30/1.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.30/1.48  thf('8', plain,
% 1.30/1.48      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 1.30/1.48      inference('sup-', [status(thm)], ['6', '7'])).
% 1.30/1.48  thf('9', plain,
% 1.30/1.48      (![X36 : $i]:
% 1.30/1.48         (~ (r2_hidden @ X36 @ (k1_relat_1 @ sk_C_2))
% 1.30/1.48          | ~ (m1_subset_1 @ X36 @ sk_B))),
% 1.30/1.48      inference('demod', [status(thm)], ['5', '8'])).
% 1.30/1.48  thf('10', plain,
% 1.30/1.48      (![X0 : $i]:
% 1.30/1.48         (((X0) = (k1_relat_1 @ sk_C_2))
% 1.30/1.48          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 1.30/1.48          | ~ (m1_subset_1 @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 1.30/1.48      inference('sup-', [status(thm)], ['4', '9'])).
% 1.30/1.48  thf('11', plain,
% 1.30/1.48      (![X20 : $i, X23 : $i]:
% 1.30/1.48         (((X23) = (k1_relat_1 @ X20))
% 1.30/1.48          | (r2_hidden @ 
% 1.30/1.48             (k4_tarski @ (sk_C_1 @ X23 @ X20) @ (sk_D @ X23 @ X20)) @ X20)
% 1.30/1.48          | (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 1.30/1.48      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.30/1.48  thf('12', plain,
% 1.30/1.48      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.48  thf(t3_subset, axiom,
% 1.30/1.48    (![A:$i,B:$i]:
% 1.30/1.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.30/1.48  thf('13', plain,
% 1.30/1.48      (![X10 : $i, X11 : $i]:
% 1.30/1.48         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.30/1.48      inference('cnf', [status(esa)], [t3_subset])).
% 1.30/1.48  thf('14', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_B @ sk_A))),
% 1.30/1.48      inference('sup-', [status(thm)], ['12', '13'])).
% 1.30/1.48  thf(d3_tarski, axiom,
% 1.30/1.48    (![A:$i,B:$i]:
% 1.30/1.48     ( ( r1_tarski @ A @ B ) <=>
% 1.30/1.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.30/1.48  thf('15', plain,
% 1.30/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.48         (~ (r2_hidden @ X0 @ X1)
% 1.30/1.48          | (r2_hidden @ X0 @ X2)
% 1.30/1.48          | ~ (r1_tarski @ X1 @ X2))),
% 1.30/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.48  thf('16', plain,
% 1.30/1.48      (![X0 : $i]:
% 1.30/1.48         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 1.30/1.48          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 1.30/1.48      inference('sup-', [status(thm)], ['14', '15'])).
% 1.30/1.48  thf('17', plain,
% 1.30/1.48      (![X0 : $i]:
% 1.30/1.48         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 1.30/1.48          | ((X0) = (k1_relat_1 @ sk_C_2))
% 1.30/1.48          | (r2_hidden @ 
% 1.30/1.48             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ (sk_D @ X0 @ sk_C_2)) @ 
% 1.30/1.48             (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.48      inference('sup-', [status(thm)], ['11', '16'])).
% 1.30/1.48  thf(l54_zfmisc_1, axiom,
% 1.30/1.48    (![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.30/1.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.30/1.48  thf('18', plain,
% 1.30/1.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.30/1.48         ((r2_hidden @ X5 @ X6)
% 1.30/1.48          | ~ (r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X8)))),
% 1.30/1.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.30/1.48  thf('19', plain,
% 1.30/1.48      (![X0 : $i]:
% 1.30/1.48         (((X0) = (k1_relat_1 @ sk_C_2))
% 1.30/1.48          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 1.30/1.48          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 1.30/1.48      inference('sup-', [status(thm)], ['17', '18'])).
% 1.30/1.48  thf('20', plain,
% 1.30/1.48      (![X1 : $i, X3 : $i]:
% 1.30/1.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.30/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.48  thf('21', plain,
% 1.30/1.48      (![X1 : $i, X3 : $i]:
% 1.30/1.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.30/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.48  thf('22', plain,
% 1.30/1.48      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.30/1.48      inference('sup-', [status(thm)], ['20', '21'])).
% 1.30/1.48  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.30/1.48      inference('simplify', [status(thm)], ['22'])).
% 1.30/1.48  thf('24', plain,
% 1.30/1.48      (![X10 : $i, X12 : $i]:
% 1.30/1.48         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.30/1.48      inference('cnf', [status(esa)], [t3_subset])).
% 1.30/1.48  thf('25', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.30/1.48      inference('sup-', [status(thm)], ['23', '24'])).
% 1.30/1.48  thf(t4_subset, axiom,
% 1.30/1.48    (![A:$i,B:$i,C:$i]:
% 1.30/1.48     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.30/1.48       ( m1_subset_1 @ A @ C ) ))).
% 1.30/1.48  thf('26', plain,
% 1.30/1.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.30/1.48         (~ (r2_hidden @ X13 @ X14)
% 1.30/1.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.30/1.48          | (m1_subset_1 @ X13 @ X15))),
% 1.30/1.48      inference('cnf', [status(esa)], [t4_subset])).
% 1.30/1.48  thf('27', plain,
% 1.30/1.48      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.30/1.48      inference('sup-', [status(thm)], ['25', '26'])).
% 1.30/1.48  thf('28', plain,
% 1.30/1.48      (![X0 : $i]:
% 1.30/1.48         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 1.30/1.48          | ((X0) = (k1_relat_1 @ sk_C_2))
% 1.30/1.48          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 1.30/1.48      inference('sup-', [status(thm)], ['19', '27'])).
% 1.30/1.48  thf('29', plain,
% 1.30/1.48      (![X0 : $i]:
% 1.30/1.48         ((r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 1.30/1.48          | ((X0) = (k1_relat_1 @ sk_C_2)))),
% 1.30/1.48      inference('clc', [status(thm)], ['10', '28'])).
% 1.30/1.48  thf(t7_ordinal1, axiom,
% 1.30/1.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.30/1.48  thf('30', plain,
% 1.30/1.48      (![X28 : $i, X29 : $i]:
% 1.30/1.48         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 1.30/1.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.30/1.48  thf('31', plain,
% 1.30/1.48      (![X0 : $i]:
% 1.30/1.48         (((X0) = (k1_relat_1 @ sk_C_2))
% 1.30/1.48          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X0 @ sk_C_2)))),
% 1.30/1.48      inference('sup-', [status(thm)], ['29', '30'])).
% 1.30/1.48  thf('32', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_2))),
% 1.30/1.48      inference('sup-', [status(thm)], ['0', '31'])).
% 1.30/1.48  thf(t65_relat_1, axiom,
% 1.30/1.48    (![A:$i]:
% 1.30/1.48     ( ( v1_relat_1 @ A ) =>
% 1.30/1.48       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 1.30/1.48         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 1.30/1.48  thf('33', plain,
% 1.30/1.48      (![X27 : $i]:
% 1.30/1.48         (((k1_relat_1 @ X27) != (k1_xboole_0))
% 1.30/1.48          | ((k2_relat_1 @ X27) = (k1_xboole_0))
% 1.30/1.48          | ~ (v1_relat_1 @ X27))),
% 1.30/1.48      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.30/1.48  thf('34', plain,
% 1.30/1.48      ((((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.48        | ~ (v1_relat_1 @ sk_C_2)
% 1.30/1.48        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 1.30/1.48      inference('sup-', [status(thm)], ['32', '33'])).
% 1.30/1.48  thf('35', plain,
% 1.30/1.48      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.48  thf(cc2_relat_1, axiom,
% 1.30/1.48    (![A:$i]:
% 1.30/1.48     ( ( v1_relat_1 @ A ) =>
% 1.30/1.48       ( ![B:$i]:
% 1.30/1.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.30/1.48  thf('36', plain,
% 1.30/1.48      (![X16 : $i, X17 : $i]:
% 1.30/1.48         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.30/1.48          | (v1_relat_1 @ X16)
% 1.30/1.48          | ~ (v1_relat_1 @ X17))),
% 1.30/1.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.30/1.48  thf('37', plain,
% 1.30/1.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_2))),
% 1.30/1.48      inference('sup-', [status(thm)], ['35', '36'])).
% 1.30/1.48  thf(fc6_relat_1, axiom,
% 1.30/1.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.30/1.48  thf('38', plain,
% 1.30/1.48      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 1.30/1.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.30/1.48  thf('39', plain, ((v1_relat_1 @ sk_C_2)),
% 1.30/1.48      inference('demod', [status(thm)], ['37', '38'])).
% 1.30/1.48  thf('40', plain,
% 1.30/1.48      ((((k1_xboole_0) != (k1_xboole_0))
% 1.30/1.48        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 1.30/1.48      inference('demod', [status(thm)], ['34', '39'])).
% 1.30/1.48  thf('41', plain, (((k2_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 1.30/1.48      inference('simplify', [status(thm)], ['40'])).
% 1.30/1.48  thf('42', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) != (k1_xboole_0))),
% 1.30/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.48  thf('43', plain,
% 1.30/1.48      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.48  thf(redefinition_k2_relset_1, axiom,
% 1.30/1.48    (![A:$i,B:$i,C:$i]:
% 1.30/1.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.30/1.48  thf('44', plain,
% 1.30/1.48      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.30/1.48         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 1.30/1.48          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.30/1.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.30/1.48  thf('45', plain,
% 1.30/1.48      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 1.30/1.48      inference('sup-', [status(thm)], ['43', '44'])).
% 1.30/1.48  thf('46', plain, (((k2_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 1.30/1.48      inference('demod', [status(thm)], ['42', '45'])).
% 1.30/1.48  thf('47', plain, ($false),
% 1.30/1.48      inference('simplify_reflect-', [status(thm)], ['41', '46'])).
% 1.30/1.48  
% 1.30/1.48  % SZS output end Refutation
% 1.30/1.48  
% 1.30/1.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
