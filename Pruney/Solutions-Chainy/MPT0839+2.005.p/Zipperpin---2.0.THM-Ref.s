%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GUYUafbAK6

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:11 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 257 expanded)
%              Number of leaves         :   35 (  91 expanded)
%              Depth                    :   19
%              Number of atoms          :  514 (2461 expanded)
%              Number of equality atoms :   21 (  84 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X36: $i] :
      ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['17','30'])).

thf('32',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','36'])).

thf('38',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['0','45'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X19: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('48',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GUYUafbAK6
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:51:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 134 iterations in 0.053s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(d1_xboole_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.49  thf(fc4_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X4 : $i, X5 : $i]:
% 0.19/0.49         (~ (v1_xboole_0 @ X4) | (v1_xboole_0 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.19/0.49  thf(l13_xboole_0, axiom,
% 0.19/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf(dt_k2_subset_1, axiom,
% 0.19/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.49  thf('5', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.19/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.49  thf('6', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.19/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf(t3_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]:
% 0.19/0.49         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.49  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf(t50_relset_1, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.49               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49                    ( ![D:$i]:
% 0.19/0.49                      ( ( m1_subset_1 @ D @ B ) =>
% 0.19/0.49                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.49              ( ![C:$i]:
% 0.19/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.49                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49                       ( ![D:$i]:
% 0.19/0.49                         ( ( m1_subset_1 @ D @ B ) =>
% 0.19/0.49                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t13_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.19/0.49       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.19/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.19/0.49          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.19/0.49          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.19/0.49      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.19/0.49          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X36 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X36 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C))
% 0.19/0.49          | ~ (m1_subset_1 @ X36 @ sk_B_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.49         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.19/0.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X36 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X36 @ (k1_relat_1 @ sk_C))
% 0.19/0.49          | ~ (m1_subset_1 @ X36 @ sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc2_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.49         ((v4_relat_1 @ X23 @ X24)
% 0.19/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.49  thf('20', plain, ((v4_relat_1 @ sk_C @ sk_B_1)),
% 0.19/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.49  thf(d18_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i]:
% 0.19/0.49         (~ (v4_relat_1 @ X17 @ X18)
% 0.19/0.49          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.19/0.49          | ~ (v1_relat_1 @ X17))),
% 0.19/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc1_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( v1_relat_1 @ C ) ))).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.49         ((v1_relat_1 @ X20)
% 0.19/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.49  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B_1)),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X8 : $i, X10 : $i]:
% 0.19/0.49         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf(t4_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.19/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X11 @ X12)
% 0.19/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.19/0.49          | (m1_subset_1 @ X11 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.19/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain, (![X36 : $i]: ~ (r2_hidden @ X36 @ (k1_relat_1 @ sk_C))),
% 0.19/0.49      inference('clc', [status(thm)], ['17', '30'])).
% 0.19/0.49  thf('32', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['12', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.49  thf('34', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.19/0.49          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['11', '34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.19/0.49        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['3', '36'])).
% 0.19/0.49  thf('38', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['12', '31'])).
% 0.19/0.49  thf('39', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['37', '40'])).
% 0.19/0.49  thf(t5_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.19/0.49          ( v1_xboole_0 @ C ) ) ))).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X14 @ X15)
% 0.19/0.49          | ~ (v1_xboole_0 @ X16)
% 0.19/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['43', '44'])).
% 0.19/0.49  thf('46', plain, ((v1_xboole_0 @ sk_C)),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '45'])).
% 0.19/0.49  thf(fc11_relat_1, axiom,
% 0.19/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X19 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (k2_relat_1 @ X19)) | ~ (v1_xboole_0 @ X19))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.49  thf('50', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['46', '49'])).
% 0.19/0.49  thf('51', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.49         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.19/0.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.49  thf('54', plain,
% 0.19/0.49      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.49  thf('55', plain, (((k2_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['51', '54'])).
% 0.19/0.49  thf('56', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['50', '55'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
