%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7jpXg3AvzL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:48 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 125 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  518 ( 816 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X30: $i] :
      ( ( ( k3_relat_1 @ X30 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v5_relat_1 @ X28 @ X29 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['11','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X15 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( m1_subset_1 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v4_relat_1 @ X26 @ X27 )
      | ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('39',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('45',plain,(
    r2_hidden @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','51'])).

thf('53',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('55',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7jpXg3AvzL
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.47/1.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.47/1.64  % Solved by: fo/fo7.sh
% 1.47/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.47/1.64  % done 2721 iterations in 1.181s
% 1.47/1.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.47/1.64  % SZS output start Refutation
% 1.47/1.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.47/1.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.47/1.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.47/1.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.47/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.47/1.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.47/1.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.47/1.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.47/1.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.47/1.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.47/1.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.47/1.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.47/1.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.47/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.47/1.64  thf(sk_C_type, type, sk_C: $i).
% 1.47/1.64  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.47/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.47/1.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.47/1.64  thf(t19_relset_1, conjecture,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.47/1.64       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.47/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.47/1.64    (~( ![A:$i,B:$i,C:$i]:
% 1.47/1.64        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.47/1.64          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.47/1.64    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 1.47/1.64  thf('0', plain,
% 1.47/1.64      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf(d6_relat_1, axiom,
% 1.47/1.64    (![A:$i]:
% 1.47/1.64     ( ( v1_relat_1 @ A ) =>
% 1.47/1.64       ( ( k3_relat_1 @ A ) =
% 1.47/1.64         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.47/1.64  thf('1', plain,
% 1.47/1.64      (![X30 : $i]:
% 1.47/1.64         (((k3_relat_1 @ X30)
% 1.47/1.64            = (k2_xboole_0 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30)))
% 1.47/1.64          | ~ (v1_relat_1 @ X30))),
% 1.47/1.64      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.47/1.64  thf(commutativity_k2_tarski, axiom,
% 1.47/1.64    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.47/1.64  thf('2', plain,
% 1.47/1.64      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 1.47/1.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.47/1.64  thf(l51_zfmisc_1, axiom,
% 1.47/1.64    (![A:$i,B:$i]:
% 1.47/1.64     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.47/1.64  thf('3', plain,
% 1.47/1.64      (![X9 : $i, X10 : $i]:
% 1.47/1.64         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 1.47/1.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.47/1.64  thf('4', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i]:
% 1.47/1.64         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.47/1.64      inference('sup+', [status(thm)], ['2', '3'])).
% 1.47/1.64  thf('5', plain,
% 1.47/1.64      (![X9 : $i, X10 : $i]:
% 1.47/1.64         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 1.47/1.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.47/1.64  thf('6', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.47/1.64      inference('sup+', [status(thm)], ['4', '5'])).
% 1.47/1.64  thf('7', plain,
% 1.47/1.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf(cc2_relset_1, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.47/1.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.47/1.64  thf('8', plain,
% 1.47/1.64      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.47/1.64         ((v5_relat_1 @ X34 @ X36)
% 1.47/1.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.47/1.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.47/1.64  thf('9', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 1.47/1.64      inference('sup-', [status(thm)], ['7', '8'])).
% 1.47/1.64  thf(d19_relat_1, axiom,
% 1.47/1.64    (![A:$i,B:$i]:
% 1.47/1.64     ( ( v1_relat_1 @ B ) =>
% 1.47/1.64       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.47/1.64  thf('10', plain,
% 1.47/1.64      (![X28 : $i, X29 : $i]:
% 1.47/1.64         (~ (v5_relat_1 @ X28 @ X29)
% 1.47/1.64          | (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 1.47/1.64          | ~ (v1_relat_1 @ X28))),
% 1.47/1.64      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.47/1.64  thf('11', plain,
% 1.47/1.64      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 1.47/1.64      inference('sup-', [status(thm)], ['9', '10'])).
% 1.47/1.64  thf('12', plain,
% 1.47/1.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf(cc1_relset_1, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.47/1.64       ( v1_relat_1 @ C ) ))).
% 1.47/1.64  thf('13', plain,
% 1.47/1.64      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.47/1.64         ((v1_relat_1 @ X31)
% 1.47/1.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.47/1.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.47/1.64  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 1.47/1.64      inference('sup-', [status(thm)], ['12', '13'])).
% 1.47/1.64  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 1.47/1.64      inference('demod', [status(thm)], ['11', '14'])).
% 1.47/1.64  thf(t3_subset, axiom,
% 1.47/1.64    (![A:$i,B:$i]:
% 1.47/1.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.47/1.64  thf('16', plain,
% 1.47/1.64      (![X20 : $i, X22 : $i]:
% 1.47/1.64         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.47/1.64      inference('cnf', [status(esa)], [t3_subset])).
% 1.47/1.64  thf('17', plain,
% 1.47/1.64      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 1.47/1.64      inference('sup-', [status(thm)], ['15', '16'])).
% 1.47/1.64  thf(t2_subset, axiom,
% 1.47/1.64    (![A:$i,B:$i]:
% 1.47/1.64     ( ( m1_subset_1 @ A @ B ) =>
% 1.47/1.64       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.47/1.64  thf('18', plain,
% 1.47/1.64      (![X18 : $i, X19 : $i]:
% 1.47/1.64         ((r2_hidden @ X18 @ X19)
% 1.47/1.64          | (v1_xboole_0 @ X19)
% 1.47/1.64          | ~ (m1_subset_1 @ X18 @ X19))),
% 1.47/1.64      inference('cnf', [status(esa)], [t2_subset])).
% 1.47/1.64  thf('19', plain,
% 1.47/1.64      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 1.47/1.64        | (r2_hidden @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['17', '18'])).
% 1.47/1.64  thf(fc1_subset_1, axiom,
% 1.47/1.64    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.47/1.64  thf('20', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 1.47/1.64      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.47/1.64  thf('21', plain, ((r2_hidden @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 1.47/1.64      inference('clc', [status(thm)], ['19', '20'])).
% 1.47/1.64  thf(t7_xboole_1, axiom,
% 1.47/1.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.47/1.64  thf('22', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 1.47/1.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.47/1.64  thf(t79_zfmisc_1, axiom,
% 1.47/1.64    (![A:$i,B:$i]:
% 1.47/1.64     ( ( r1_tarski @ A @ B ) =>
% 1.47/1.64       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.47/1.64  thf('23', plain,
% 1.47/1.64      (![X15 : $i, X16 : $i]:
% 1.47/1.64         ((r1_tarski @ (k1_zfmisc_1 @ X15) @ (k1_zfmisc_1 @ X16))
% 1.47/1.64          | ~ (r1_tarski @ X15 @ X16))),
% 1.47/1.64      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.47/1.64  thf('24', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i]:
% 1.47/1.64         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 1.47/1.64          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['22', '23'])).
% 1.47/1.64  thf('25', plain,
% 1.47/1.64      (![X20 : $i, X22 : $i]:
% 1.47/1.64         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.47/1.64      inference('cnf', [status(esa)], [t3_subset])).
% 1.47/1.64  thf('26', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i]:
% 1.47/1.64         (m1_subset_1 @ (k1_zfmisc_1 @ X1) @ 
% 1.47/1.64          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.47/1.64      inference('sup-', [status(thm)], ['24', '25'])).
% 1.47/1.64  thf(t4_subset, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.47/1.64       ( m1_subset_1 @ A @ C ) ))).
% 1.47/1.64  thf('27', plain,
% 1.47/1.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.47/1.64         (~ (r2_hidden @ X23 @ X24)
% 1.47/1.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 1.47/1.64          | (m1_subset_1 @ X23 @ X25))),
% 1.47/1.64      inference('cnf', [status(esa)], [t4_subset])).
% 1.47/1.64  thf('28', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.47/1.64         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.47/1.64          | ~ (r2_hidden @ X2 @ (k1_zfmisc_1 @ X1)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['26', '27'])).
% 1.47/1.64  thf('29', plain,
% 1.47/1.64      (![X0 : $i]:
% 1.47/1.64         (m1_subset_1 @ (k2_relat_1 @ sk_C) @ 
% 1.47/1.64          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['21', '28'])).
% 1.47/1.64  thf('30', plain,
% 1.47/1.64      (![X20 : $i, X21 : $i]:
% 1.47/1.64         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t3_subset])).
% 1.47/1.64  thf('31', plain,
% 1.47/1.64      (![X0 : $i]:
% 1.47/1.64         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))),
% 1.47/1.64      inference('sup-', [status(thm)], ['29', '30'])).
% 1.47/1.64  thf('32', plain,
% 1.47/1.64      (![X0 : $i]:
% 1.47/1.64         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 1.47/1.64      inference('sup+', [status(thm)], ['6', '31'])).
% 1.47/1.64  thf('33', plain,
% 1.47/1.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('34', plain,
% 1.47/1.64      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.47/1.64         ((v4_relat_1 @ X34 @ X35)
% 1.47/1.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.47/1.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.47/1.64  thf('35', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.47/1.64      inference('sup-', [status(thm)], ['33', '34'])).
% 1.47/1.64  thf(d18_relat_1, axiom,
% 1.47/1.64    (![A:$i,B:$i]:
% 1.47/1.64     ( ( v1_relat_1 @ B ) =>
% 1.47/1.64       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.47/1.64  thf('36', plain,
% 1.47/1.64      (![X26 : $i, X27 : $i]:
% 1.47/1.64         (~ (v4_relat_1 @ X26 @ X27)
% 1.47/1.64          | (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 1.47/1.64          | ~ (v1_relat_1 @ X26))),
% 1.47/1.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.47/1.64  thf('37', plain,
% 1.47/1.64      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.47/1.64      inference('sup-', [status(thm)], ['35', '36'])).
% 1.47/1.64  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 1.47/1.64      inference('sup-', [status(thm)], ['12', '13'])).
% 1.47/1.64  thf('39', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.47/1.64      inference('demod', [status(thm)], ['37', '38'])).
% 1.47/1.64  thf('40', plain,
% 1.47/1.64      (![X20 : $i, X22 : $i]:
% 1.47/1.64         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.47/1.64      inference('cnf', [status(esa)], [t3_subset])).
% 1.47/1.64  thf('41', plain,
% 1.47/1.64      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.47/1.64      inference('sup-', [status(thm)], ['39', '40'])).
% 1.47/1.64  thf('42', plain,
% 1.47/1.64      (![X18 : $i, X19 : $i]:
% 1.47/1.64         ((r2_hidden @ X18 @ X19)
% 1.47/1.64          | (v1_xboole_0 @ X19)
% 1.47/1.64          | ~ (m1_subset_1 @ X18 @ X19))),
% 1.47/1.64      inference('cnf', [status(esa)], [t2_subset])).
% 1.47/1.64  thf('43', plain,
% 1.47/1.64      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.47/1.64        | (r2_hidden @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['41', '42'])).
% 1.47/1.64  thf('44', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 1.47/1.64      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.47/1.64  thf('45', plain, ((r2_hidden @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.47/1.64      inference('clc', [status(thm)], ['43', '44'])).
% 1.47/1.64  thf('46', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.47/1.64         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.47/1.64          | ~ (r2_hidden @ X2 @ (k1_zfmisc_1 @ X1)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['26', '27'])).
% 1.47/1.64  thf('47', plain,
% 1.47/1.64      (![X0 : $i]:
% 1.47/1.64         (m1_subset_1 @ (k1_relat_1 @ sk_C) @ 
% 1.47/1.64          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['45', '46'])).
% 1.47/1.64  thf('48', plain,
% 1.47/1.64      (![X20 : $i, X21 : $i]:
% 1.47/1.64         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t3_subset])).
% 1.47/1.64  thf('49', plain,
% 1.47/1.64      (![X0 : $i]:
% 1.47/1.64         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 1.47/1.64      inference('sup-', [status(thm)], ['47', '48'])).
% 1.47/1.64  thf(t8_xboole_1, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.47/1.64       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.47/1.64  thf('50', plain,
% 1.47/1.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.47/1.64         (~ (r1_tarski @ X2 @ X3)
% 1.47/1.64          | ~ (r1_tarski @ X4 @ X3)
% 1.47/1.64          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 1.47/1.64      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.47/1.64  thf('51', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i]:
% 1.47/1.64         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 1.47/1.64           (k2_xboole_0 @ sk_A @ X0))
% 1.47/1.64          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['49', '50'])).
% 1.47/1.64  thf('52', plain,
% 1.47/1.64      ((r1_tarski @ 
% 1.47/1.64        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 1.47/1.64        (k2_xboole_0 @ sk_A @ sk_B))),
% 1.47/1.64      inference('sup-', [status(thm)], ['32', '51'])).
% 1.47/1.64  thf('53', plain,
% 1.47/1.64      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 1.47/1.64        | ~ (v1_relat_1 @ sk_C))),
% 1.47/1.64      inference('sup+', [status(thm)], ['1', '52'])).
% 1.47/1.64  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 1.47/1.64      inference('sup-', [status(thm)], ['12', '13'])).
% 1.47/1.64  thf('55', plain,
% 1.47/1.64      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.47/1.64      inference('demod', [status(thm)], ['53', '54'])).
% 1.47/1.64  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 1.47/1.64  
% 1.47/1.64  % SZS output end Refutation
% 1.47/1.64  
% 1.47/1.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
