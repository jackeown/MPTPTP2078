%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kLKLFUP8J5

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 192 expanded)
%              Number of leaves         :   33 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  530 (1844 expanded)
%              Number of equality atoms :   30 (  72 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X27 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ sk_B )
    | ( r1_xboole_0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    r1_xboole_0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_B @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X12 ) @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k7_relat_1 @ sk_C_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['12','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('32',plain,
    ( ( k7_relat_1 @ sk_C_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k7_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('39',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','39'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X9: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf('51',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kLKLFUP8J5
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 76 iterations in 0.038s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.48  thf(t50_relset_1, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.48               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48                    ( ![D:$i]:
% 0.19/0.48                      ( ( m1_subset_1 @ D @ B ) =>
% 0.19/0.48                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.48              ( ![C:$i]:
% 0.19/0.48                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.48                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48                       ( ![D:$i]:
% 0.19/0.48                         ( ( m1_subset_1 @ D @ B ) =>
% 0.19/0.48                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t98_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X17 : $i]:
% 0.19/0.48         (((k7_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (X17))
% 0.19/0.48          | ~ (v1_relat_1 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc2_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.48         ((v4_relat_1 @ X18 @ X19)
% 0.19/0.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.48  thf('4', plain, ((v4_relat_1 @ sk_C_1 @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf(t209_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.19/0.48          | ~ (v4_relat_1 @ X15 @ X16)
% 0.19/0.48          | ~ (v1_relat_1 @ X15))),
% 0.19/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc2_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.19/0.48          | (v1_relat_1 @ X7)
% 0.19/0.48          | ~ (v1_relat_1 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf(fc6_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.48  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '11'])).
% 0.19/0.48  thf(t3_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf(t1_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.19/0.48      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X0) | (m1_subset_1 @ (sk_C @ X0 @ X1) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X27 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))
% 0.19/0.48          | ~ (m1_subset_1 @ X27 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ 
% 0.19/0.48               (sk_C @ X0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1)) @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (((r1_xboole_0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ sk_B)
% 0.19/0.48        | (r1_xboole_0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      ((r1_xboole_0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ sk_B)),
% 0.19/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ X1)
% 0.19/0.48          | ~ (r2_hidden @ X3 @ X4)
% 0.19/0.48          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X1 @ X0)
% 0.19/0.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.19/0.48          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.19/0.48          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.19/0.48          | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['21', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      ((r1_xboole_0 @ sk_B @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['20', '26'])).
% 0.19/0.48  thf(t207_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ C ) =>
% 0.19/0.48       ( ( r1_xboole_0 @ A @ B ) =>
% 0.19/0.48         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.48         (~ (r1_xboole_0 @ X12 @ X13)
% 0.19/0.48          | ~ (v1_relat_1 @ X14)
% 0.19/0.48          | ((k7_relat_1 @ (k7_relat_1 @ X14 @ X12) @ X13) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ 
% 0.19/0.48            (k1_relset_1 @ sk_B @ sk_A @ sk_C_1)) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      ((((k7_relat_1 @ sk_C_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))
% 0.19/0.48          = (k1_xboole_0))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_C_1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['12', '29'])).
% 0.19/0.48  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (((k7_relat_1 @ sk_C_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))
% 0.19/0.48         = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.49         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.19/0.49          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (((k7_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)) = (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['32', '35'])).
% 0.19/0.49  thf('37', plain, ((((sk_C_1) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['1', '36'])).
% 0.19/0.49  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf('39', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['0', '39'])).
% 0.19/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.49         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.19/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (((k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.49  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.49  thf(fc11_relat_1, axiom,
% 0.19/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X9 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X9)) | ~ (v1_xboole_0 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.19/0.49  thf(l13_xboole_0, axiom,
% 0.19/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.49  thf('47', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '46'])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (((k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['42', '47'])).
% 0.19/0.49  thf('49', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('50', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (((k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.49  thf('52', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['48', '51'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
