%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jKeykTWNbx

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:16 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 185 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  455 (1577 expanded)
%              Number of equality atoms :   25 (  65 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(fc16_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc16_relat_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( k1_xboole_0 = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('15',plain,
    ( ( k1_xboole_0 = sk_C )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X30 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X30 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X30: $i] :
      ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','32'])).

thf('34',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['15','34'])).

thf('36',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','35'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['15','34'])).

thf('47',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jKeykTWNbx
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 135 iterations in 0.122s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(t50_relset_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.39/0.58               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.39/0.58                    ( ![D:$i]:
% 0.39/0.58                      ( ( m1_subset_1 @ D @ B ) =>
% 0.39/0.58                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.58              ( ![C:$i]:
% 0.39/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.39/0.58                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.39/0.58                       ( ![D:$i]:
% 0.39/0.58                         ( ( m1_subset_1 @ D @ B ) =>
% 0.39/0.58                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t98_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X20 : $i]:
% 0.39/0.58         (((k7_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (X20))
% 0.39/0.58          | ~ (v1_relat_1 @ X20))),
% 0.39/0.58      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(cc2_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.39/0.58          | (v1_relat_1 @ X11)
% 0.39/0.58          | ~ (v1_relat_1 @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.58  thf(fc6_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.58  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.58  thf(fc16_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_xboole_0 @ B ) ) =>
% 0.39/0.58       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.39/0.58         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X16)
% 0.39/0.58          | ~ (v1_xboole_0 @ X17)
% 0.39/0.58          | (v1_xboole_0 @ (k7_relat_1 @ X16 @ X17)))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc16_relat_1])).
% 0.39/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.58  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf(t8_boole, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t8_boole])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['7', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_xboole_0) = (k7_relat_1 @ sk_C @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      ((((k1_xboole_0) = (sk_C))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['1', '12'])).
% 0.39/0.58  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      ((((k1_xboole_0) = (sk_C)) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf(d1_xboole_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X30 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X30 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C))
% 0.39/0.58          | ~ (m1_subset_1 @ X30 @ sk_B_1))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.58         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.39/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X30 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X30 @ (k1_relat_1 @ sk_C))
% 0.39/0.58          | ~ (m1_subset_1 @ X30 @ sk_B_1))),
% 0.39/0.58      inference('demod', [status(thm)], ['17', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(cc2_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.58         ((v4_relat_1 @ X21 @ X22)
% 0.39/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.58  thf('24', plain, ((v4_relat_1 @ sk_C @ sk_B_1)),
% 0.39/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.58  thf(d18_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ B ) =>
% 0.39/0.58       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i]:
% 0.39/0.58         (~ (v4_relat_1 @ X13 @ X14)
% 0.39/0.58          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.39/0.58          | ~ (v1_relat_1 @ X13))),
% 0.39/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.58  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B_1)),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf(t3_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X5 : $i, X7 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf(t4_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.39/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.39/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.39/0.58          | (m1_subset_1 @ X8 @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('33', plain, (![X30 : $i]: ~ (r2_hidden @ X30 @ (k1_relat_1 @ sk_C))),
% 0.39/0.58      inference('clc', [status(thm)], ['21', '32'])).
% 0.39/0.58  thf('34', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '33'])).
% 0.39/0.58  thf('35', plain, (((k1_xboole_0) = (sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['15', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.39/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['0', '35'])).
% 0.39/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.58         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.39/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (((k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0)
% 0.39/0.58         = (k2_relat_1 @ k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.58  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf(fc11_relat_1, axiom,
% 0.39/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (![X15 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k2_relat_1 @ X15)) | ~ (v1_xboole_0 @ X15))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k2_relat_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.58  thf('43', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['39', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (((k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['38', '43'])).
% 0.39/0.58  thf('45', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C) != (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('46', plain, (((k1_xboole_0) = (sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['15', '34'])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (((k2_relset_1 @ sk_B_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.58  thf('48', plain, ($false),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['44', '47'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
