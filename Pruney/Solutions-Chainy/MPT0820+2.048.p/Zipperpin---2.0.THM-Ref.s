%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q4Bc39Hugs

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:54 EST 2020

% Result     : Theorem 7.18s
% Output     : Refutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 168 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  539 (1208 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t19_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_relset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( ( k3_relat_1 @ X19 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('5',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ~ ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('15',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['10','11'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) @ sk_A ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X3 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['10','11'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('52',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['10','11'])).

thf('55',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q4Bc39Hugs
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:09:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 7.18/7.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.18/7.41  % Solved by: fo/fo7.sh
% 7.18/7.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.18/7.41  % done 1946 iterations in 6.944s
% 7.18/7.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.18/7.41  % SZS output start Refutation
% 7.18/7.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.18/7.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.18/7.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.18/7.41  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 7.18/7.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.18/7.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.18/7.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.18/7.41  thf(sk_A_type, type, sk_A: $i).
% 7.18/7.41  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 7.18/7.41  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.18/7.41  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.18/7.41  thf(sk_B_type, type, sk_B: $i).
% 7.18/7.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.18/7.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.18/7.41  thf(sk_C_type, type, sk_C: $i).
% 7.18/7.41  thf(t19_relset_1, conjecture,
% 7.18/7.41    (![A:$i,B:$i,C:$i]:
% 7.18/7.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.18/7.41       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 7.18/7.41  thf(zf_stmt_0, negated_conjecture,
% 7.18/7.41    (~( ![A:$i,B:$i,C:$i]:
% 7.18/7.41        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.18/7.41          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 7.18/7.41    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 7.18/7.41  thf('0', plain,
% 7.18/7.41      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 7.18/7.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.18/7.41  thf(d6_relat_1, axiom,
% 7.18/7.41    (![A:$i]:
% 7.18/7.41     ( ( v1_relat_1 @ A ) =>
% 7.18/7.41       ( ( k3_relat_1 @ A ) =
% 7.18/7.41         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 7.18/7.41  thf('1', plain,
% 7.18/7.41      (![X19 : $i]:
% 7.18/7.41         (((k3_relat_1 @ X19)
% 7.18/7.41            = (k2_xboole_0 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19)))
% 7.18/7.41          | ~ (v1_relat_1 @ X19))),
% 7.18/7.41      inference('cnf', [status(esa)], [d6_relat_1])).
% 7.18/7.41  thf(t7_xboole_1, axiom,
% 7.18/7.41    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 7.18/7.41  thf('2', plain,
% 7.18/7.41      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 7.18/7.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.18/7.41  thf('3', plain,
% 7.18/7.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.18/7.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.18/7.41  thf(cc2_relset_1, axiom,
% 7.18/7.41    (![A:$i,B:$i,C:$i]:
% 7.18/7.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.18/7.41       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.18/7.41  thf('4', plain,
% 7.18/7.41      (![X26 : $i, X27 : $i, X28 : $i]:
% 7.18/7.41         ((v4_relat_1 @ X26 @ X27)
% 7.18/7.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 7.18/7.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.18/7.41  thf('5', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 7.18/7.41      inference('sup-', [status(thm)], ['3', '4'])).
% 7.18/7.41  thf(t209_relat_1, axiom,
% 7.18/7.41    (![A:$i,B:$i]:
% 7.18/7.41     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 7.18/7.41       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 7.18/7.41  thf('6', plain,
% 7.18/7.41      (![X22 : $i, X23 : $i]:
% 7.18/7.41         (((X22) = (k7_relat_1 @ X22 @ X23))
% 7.18/7.41          | ~ (v4_relat_1 @ X22 @ X23)
% 7.18/7.41          | ~ (v1_relat_1 @ X22))),
% 7.18/7.41      inference('cnf', [status(esa)], [t209_relat_1])).
% 7.18/7.41  thf('7', plain,
% 7.18/7.41      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 7.18/7.41      inference('sup-', [status(thm)], ['5', '6'])).
% 7.18/7.41  thf('8', plain,
% 7.18/7.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.18/7.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.18/7.41  thf(cc2_relat_1, axiom,
% 7.18/7.41    (![A:$i]:
% 7.18/7.41     ( ( v1_relat_1 @ A ) =>
% 7.18/7.41       ( ![B:$i]:
% 7.18/7.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 7.18/7.41  thf('9', plain,
% 7.18/7.41      (![X15 : $i, X16 : $i]:
% 7.18/7.41         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 7.18/7.41          | (v1_relat_1 @ X15)
% 7.18/7.41          | ~ (v1_relat_1 @ X16))),
% 7.18/7.41      inference('cnf', [status(esa)], [cc2_relat_1])).
% 7.18/7.41  thf('10', plain,
% 7.18/7.41      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 7.18/7.41      inference('sup-', [status(thm)], ['8', '9'])).
% 7.18/7.41  thf(fc6_relat_1, axiom,
% 7.18/7.41    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 7.18/7.41  thf('11', plain,
% 7.18/7.41      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 7.18/7.41      inference('cnf', [status(esa)], [fc6_relat_1])).
% 7.18/7.41  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 7.18/7.41      inference('demod', [status(thm)], ['10', '11'])).
% 7.18/7.41  thf('13', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 7.18/7.41      inference('demod', [status(thm)], ['7', '12'])).
% 7.18/7.41  thf(t87_relat_1, axiom,
% 7.18/7.41    (![A:$i,B:$i]:
% 7.18/7.41     ( ( v1_relat_1 @ B ) =>
% 7.18/7.41       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 7.18/7.41  thf('14', plain,
% 7.18/7.41      (![X24 : $i, X25 : $i]:
% 7.18/7.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X25)) @ X25)
% 7.18/7.41          | ~ (v1_relat_1 @ X24))),
% 7.18/7.41      inference('cnf', [status(esa)], [t87_relat_1])).
% 7.18/7.41  thf('15', plain,
% 7.18/7.41      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 7.18/7.41      inference('sup+', [status(thm)], ['13', '14'])).
% 7.18/7.41  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 7.18/7.41      inference('demod', [status(thm)], ['10', '11'])).
% 7.18/7.41  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 7.18/7.41      inference('demod', [status(thm)], ['15', '16'])).
% 7.18/7.41  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 7.18/7.41      inference('demod', [status(thm)], ['15', '16'])).
% 7.18/7.41  thf(t8_xboole_1, axiom,
% 7.18/7.41    (![A:$i,B:$i,C:$i]:
% 7.18/7.41     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 7.18/7.41       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 7.18/7.41  thf('19', plain,
% 7.18/7.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.18/7.41         (~ (r1_tarski @ X8 @ X9)
% 7.18/7.41          | ~ (r1_tarski @ X10 @ X9)
% 7.18/7.41          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 7.18/7.41      inference('cnf', [status(esa)], [t8_xboole_1])).
% 7.18/7.41  thf('20', plain,
% 7.18/7.41      (![X0 : $i]:
% 7.18/7.41         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X0) @ sk_A)
% 7.18/7.41          | ~ (r1_tarski @ X0 @ sk_A))),
% 7.18/7.41      inference('sup-', [status(thm)], ['18', '19'])).
% 7.18/7.41  thf('21', plain,
% 7.18/7.41      ((r1_tarski @ 
% 7.18/7.41        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)) @ sk_A)),
% 7.18/7.41      inference('sup-', [status(thm)], ['17', '20'])).
% 7.18/7.41  thf(t1_xboole_1, axiom,
% 7.18/7.41    (![A:$i,B:$i,C:$i]:
% 7.18/7.41     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 7.18/7.41       ( r1_tarski @ A @ C ) ))).
% 7.18/7.41  thf('22', plain,
% 7.18/7.41      (![X3 : $i, X4 : $i, X5 : $i]:
% 7.18/7.41         (~ (r1_tarski @ X3 @ X4)
% 7.18/7.41          | ~ (r1_tarski @ X4 @ X5)
% 7.18/7.41          | (r1_tarski @ X3 @ X5))),
% 7.18/7.41      inference('cnf', [status(esa)], [t1_xboole_1])).
% 7.18/7.41  thf('23', plain,
% 7.18/7.41      (![X0 : $i]:
% 7.18/7.41         ((r1_tarski @ 
% 7.18/7.41           (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)) @ X0)
% 7.18/7.41          | ~ (r1_tarski @ sk_A @ X0))),
% 7.18/7.41      inference('sup-', [status(thm)], ['21', '22'])).
% 7.18/7.41  thf('24', plain,
% 7.18/7.41      (![X0 : $i]:
% 7.18/7.41         (r1_tarski @ 
% 7.18/7.41          (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)) @ 
% 7.18/7.41          (k2_xboole_0 @ sk_A @ X0))),
% 7.18/7.41      inference('sup-', [status(thm)], ['2', '23'])).
% 7.18/7.41  thf('25', plain,
% 7.18/7.41      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 7.18/7.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.18/7.41  thf('26', plain,
% 7.18/7.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.18/7.41         (~ (r1_tarski @ X8 @ X9)
% 7.18/7.41          | ~ (r1_tarski @ X10 @ X9)
% 7.18/7.41          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 7.18/7.41      inference('cnf', [status(esa)], [t8_xboole_1])).
% 7.18/7.41  thf('27', plain,
% 7.18/7.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.18/7.41         ((r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 7.18/7.41          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.18/7.41      inference('sup-', [status(thm)], ['25', '26'])).
% 7.18/7.41  thf('28', plain,
% 7.18/7.41      (![X0 : $i]:
% 7.18/7.41         (r1_tarski @ 
% 7.18/7.41          (k2_xboole_0 @ sk_A @ 
% 7.18/7.41           (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))) @ 
% 7.18/7.41          (k2_xboole_0 @ sk_A @ X0))),
% 7.18/7.41      inference('sup-', [status(thm)], ['24', '27'])).
% 7.18/7.41  thf('29', plain,
% 7.18/7.41      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 7.18/7.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.18/7.41  thf('30', plain,
% 7.18/7.41      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 7.18/7.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.18/7.41  thf(t10_xboole_1, axiom,
% 7.18/7.41    (![A:$i,B:$i,C:$i]:
% 7.18/7.41     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 7.18/7.41  thf('31', plain,
% 7.18/7.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.18/7.41         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 7.18/7.41      inference('cnf', [status(esa)], [t10_xboole_1])).
% 7.18/7.41  thf('32', plain,
% 7.18/7.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.18/7.41         (r1_tarski @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.18/7.41      inference('sup-', [status(thm)], ['30', '31'])).
% 7.18/7.41  thf('33', plain,
% 7.18/7.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.18/7.41         (~ (r1_tarski @ X8 @ X9)
% 7.18/7.41          | ~ (r1_tarski @ X10 @ X9)
% 7.18/7.41          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 7.18/7.41      inference('cnf', [status(esa)], [t8_xboole_1])).
% 7.18/7.41  thf('34', plain,
% 7.18/7.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.18/7.41         ((r1_tarski @ (k2_xboole_0 @ X1 @ X3) @ 
% 7.18/7.41           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 7.18/7.41          | ~ (r1_tarski @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 7.18/7.41      inference('sup-', [status(thm)], ['32', '33'])).
% 7.18/7.41  thf('35', plain,
% 7.18/7.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.18/7.41         (r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ 
% 7.18/7.41          (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.18/7.41      inference('sup-', [status(thm)], ['29', '34'])).
% 7.18/7.41  thf('36', plain,
% 7.18/7.41      (![X3 : $i, X4 : $i, X5 : $i]:
% 7.18/7.41         (~ (r1_tarski @ X3 @ X4)
% 7.18/7.41          | ~ (r1_tarski @ X4 @ X5)
% 7.18/7.41          | (r1_tarski @ X3 @ X5))),
% 7.18/7.41      inference('cnf', [status(esa)], [t1_xboole_1])).
% 7.18/7.41  thf('37', plain,
% 7.18/7.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.18/7.41         ((r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ X3)
% 7.18/7.41          | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3))),
% 7.18/7.41      inference('sup-', [status(thm)], ['35', '36'])).
% 7.18/7.41  thf('38', plain,
% 7.18/7.41      (![X0 : $i]:
% 7.18/7.41         (r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) @ 
% 7.18/7.41          (k2_xboole_0 @ sk_A @ X0))),
% 7.18/7.41      inference('sup-', [status(thm)], ['28', '37'])).
% 7.18/7.41  thf('39', plain,
% 7.18/7.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.18/7.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.18/7.41  thf('40', plain,
% 7.18/7.41      (![X26 : $i, X27 : $i, X28 : $i]:
% 7.18/7.41         ((v5_relat_1 @ X26 @ X28)
% 7.18/7.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 7.18/7.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.18/7.41  thf('41', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 7.18/7.41      inference('sup-', [status(thm)], ['39', '40'])).
% 7.18/7.41  thf(d19_relat_1, axiom,
% 7.18/7.41    (![A:$i,B:$i]:
% 7.18/7.41     ( ( v1_relat_1 @ B ) =>
% 7.18/7.41       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 7.18/7.41  thf('42', plain,
% 7.18/7.41      (![X17 : $i, X18 : $i]:
% 7.18/7.41         (~ (v5_relat_1 @ X17 @ X18)
% 7.18/7.41          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 7.18/7.41          | ~ (v1_relat_1 @ X17))),
% 7.18/7.41      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.18/7.41  thf('43', plain,
% 7.18/7.41      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 7.18/7.41      inference('sup-', [status(thm)], ['41', '42'])).
% 7.18/7.41  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 7.18/7.41      inference('demod', [status(thm)], ['10', '11'])).
% 7.18/7.41  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 7.18/7.41      inference('demod', [status(thm)], ['43', '44'])).
% 7.18/7.41  thf('46', plain,
% 7.18/7.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.18/7.41         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 7.18/7.41      inference('cnf', [status(esa)], [t10_xboole_1])).
% 7.18/7.41  thf('47', plain,
% 7.18/7.41      (![X0 : $i]:
% 7.18/7.41         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 7.18/7.41      inference('sup-', [status(thm)], ['45', '46'])).
% 7.18/7.41  thf('48', plain,
% 7.18/7.41      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.18/7.41         (~ (r1_tarski @ X8 @ X9)
% 7.18/7.41          | ~ (r1_tarski @ X10 @ X9)
% 7.18/7.41          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 7.18/7.41      inference('cnf', [status(esa)], [t8_xboole_1])).
% 7.18/7.41  thf('49', plain,
% 7.18/7.41      (![X0 : $i, X1 : $i]:
% 7.18/7.41         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X1) @ 
% 7.18/7.41           (k2_xboole_0 @ X0 @ sk_B))
% 7.18/7.41          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_B)))),
% 7.18/7.41      inference('sup-', [status(thm)], ['47', '48'])).
% 7.18/7.41  thf('50', plain,
% 7.18/7.41      ((r1_tarski @ 
% 7.18/7.41        (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 7.18/7.41         (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A)) @ 
% 7.18/7.41        (k2_xboole_0 @ sk_A @ sk_B))),
% 7.18/7.41      inference('sup-', [status(thm)], ['38', '49'])).
% 7.18/7.41  thf('51', plain,
% 7.18/7.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.18/7.41         ((r1_tarski @ (k2_xboole_0 @ X1 @ X2) @ X3)
% 7.18/7.41          | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3))),
% 7.18/7.41      inference('sup-', [status(thm)], ['35', '36'])).
% 7.18/7.41  thf('52', plain,
% 7.18/7.41      ((r1_tarski @ 
% 7.18/7.41        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 7.18/7.41        (k2_xboole_0 @ sk_A @ sk_B))),
% 7.18/7.41      inference('sup-', [status(thm)], ['50', '51'])).
% 7.18/7.41  thf('53', plain,
% 7.18/7.41      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 7.18/7.41        | ~ (v1_relat_1 @ sk_C))),
% 7.18/7.41      inference('sup+', [status(thm)], ['1', '52'])).
% 7.18/7.41  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 7.18/7.41      inference('demod', [status(thm)], ['10', '11'])).
% 7.18/7.41  thf('55', plain,
% 7.18/7.41      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 7.18/7.41      inference('demod', [status(thm)], ['53', '54'])).
% 7.18/7.41  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 7.18/7.41  
% 7.18/7.41  % SZS output end Refutation
% 7.18/7.41  
% 7.25/7.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
