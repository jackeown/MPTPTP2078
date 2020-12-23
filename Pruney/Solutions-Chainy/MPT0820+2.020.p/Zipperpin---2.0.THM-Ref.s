%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ZYD7QnguM

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:50 EST 2020

% Result     : Theorem 2.53s
% Output     : Refutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 128 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  523 ( 887 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( ( ( k3_relat_1 @ X32 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ ( k2_xboole_0 @ X15 @ X17 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X15 ) @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('12',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X19 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ X22 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','20'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','23'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v5_relat_1 @ X30 @ X31 )
      | ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_relat_1 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X15 @ X17 ) @ X16 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v4_relat_1 @ X28 @ X29 )
      | ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X8 @ X7 )
      | ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('47',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ZYD7QnguM
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.53/2.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.53/2.80  % Solved by: fo/fo7.sh
% 2.53/2.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.53/2.80  % done 3099 iterations in 2.353s
% 2.53/2.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.53/2.80  % SZS output start Refutation
% 2.53/2.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.53/2.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.53/2.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.53/2.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.53/2.80  thf(sk_A_type, type, sk_A: $i).
% 2.53/2.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.53/2.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.53/2.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.53/2.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.53/2.80  thf(sk_B_type, type, sk_B: $i).
% 2.53/2.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.53/2.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.53/2.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.53/2.80  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.53/2.80  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.53/2.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.53/2.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.53/2.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.53/2.80  thf(t19_relset_1, conjecture,
% 2.53/2.80    (![A:$i,B:$i,C:$i]:
% 2.53/2.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.53/2.80       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.53/2.80  thf(zf_stmt_0, negated_conjecture,
% 2.53/2.80    (~( ![A:$i,B:$i,C:$i]:
% 2.53/2.80        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.53/2.80          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 2.53/2.80    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 2.53/2.80  thf('0', plain,
% 2.53/2.80      (~ (r1_tarski @ (k3_relat_1 @ sk_C_1) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.53/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.80  thf(d6_relat_1, axiom,
% 2.53/2.80    (![A:$i]:
% 2.53/2.80     ( ( v1_relat_1 @ A ) =>
% 2.53/2.80       ( ( k3_relat_1 @ A ) =
% 2.53/2.80         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.53/2.80  thf('1', plain,
% 2.53/2.80      (![X32 : $i]:
% 2.53/2.80         (((k3_relat_1 @ X32)
% 2.53/2.80            = (k2_xboole_0 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32)))
% 2.53/2.80          | ~ (v1_relat_1 @ X32))),
% 2.53/2.80      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.53/2.80  thf(commutativity_k2_tarski, axiom,
% 2.53/2.80    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.53/2.80  thf('2', plain,
% 2.53/2.80      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 2.53/2.80      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.53/2.80  thf(l51_zfmisc_1, axiom,
% 2.53/2.80    (![A:$i,B:$i]:
% 2.53/2.80     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.53/2.80  thf('3', plain,
% 2.53/2.80      (![X13 : $i, X14 : $i]:
% 2.53/2.80         ((k3_tarski @ (k2_tarski @ X13 @ X14)) = (k2_xboole_0 @ X13 @ X14))),
% 2.53/2.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.53/2.80  thf('4', plain,
% 2.53/2.80      (![X0 : $i, X1 : $i]:
% 2.53/2.80         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.53/2.80      inference('sup+', [status(thm)], ['2', '3'])).
% 2.53/2.80  thf('5', plain,
% 2.53/2.80      (![X13 : $i, X14 : $i]:
% 2.53/2.80         ((k3_tarski @ (k2_tarski @ X13 @ X14)) = (k2_xboole_0 @ X13 @ X14))),
% 2.53/2.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.53/2.80  thf('6', plain,
% 2.53/2.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.53/2.80      inference('sup+', [status(thm)], ['4', '5'])).
% 2.53/2.80  thf(t120_zfmisc_1, axiom,
% 2.53/2.80    (![A:$i,B:$i,C:$i]:
% 2.53/2.80     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 2.53/2.80         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 2.53/2.80       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.53/2.80         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 2.53/2.80  thf('7', plain,
% 2.53/2.80      (![X15 : $i, X17 : $i, X18 : $i]:
% 2.53/2.80         ((k2_zfmisc_1 @ X18 @ (k2_xboole_0 @ X15 @ X17))
% 2.53/2.80           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X15) @ 
% 2.53/2.80              (k2_zfmisc_1 @ X18 @ X17)))),
% 2.53/2.80      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 2.53/2.80  thf('8', plain,
% 2.53/2.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.53/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.80  thf(t2_subset, axiom,
% 2.53/2.80    (![A:$i,B:$i]:
% 2.53/2.80     ( ( m1_subset_1 @ A @ B ) =>
% 2.53/2.80       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 2.53/2.80  thf('9', plain,
% 2.53/2.80      (![X24 : $i, X25 : $i]:
% 2.53/2.80         ((r2_hidden @ X24 @ X25)
% 2.53/2.80          | (v1_xboole_0 @ X25)
% 2.53/2.80          | ~ (m1_subset_1 @ X24 @ X25))),
% 2.53/2.80      inference('cnf', [status(esa)], [t2_subset])).
% 2.53/2.80  thf('10', plain,
% 2.53/2.80      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.53/2.80        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 2.53/2.80      inference('sup-', [status(thm)], ['8', '9'])).
% 2.53/2.80  thf(fc1_subset_1, axiom,
% 2.53/2.80    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.53/2.80  thf('11', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 2.53/2.80      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.53/2.80  thf('12', plain,
% 2.53/2.80      ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.53/2.80      inference('clc', [status(thm)], ['10', '11'])).
% 2.53/2.80  thf(t7_xboole_1, axiom,
% 2.53/2.80    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.53/2.80  thf('13', plain,
% 2.53/2.80      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 2.53/2.80      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.53/2.80  thf(t79_zfmisc_1, axiom,
% 2.53/2.80    (![A:$i,B:$i]:
% 2.53/2.80     ( ( r1_tarski @ A @ B ) =>
% 2.53/2.80       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.53/2.80  thf('14', plain,
% 2.53/2.80      (![X19 : $i, X20 : $i]:
% 2.53/2.80         ((r1_tarski @ (k1_zfmisc_1 @ X19) @ (k1_zfmisc_1 @ X20))
% 2.53/2.80          | ~ (r1_tarski @ X19 @ X20))),
% 2.53/2.80      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 2.53/2.80  thf('15', plain,
% 2.53/2.80      (![X0 : $i, X1 : $i]:
% 2.53/2.80         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 2.53/2.80          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.53/2.80      inference('sup-', [status(thm)], ['13', '14'])).
% 2.53/2.80  thf(d3_tarski, axiom,
% 2.53/2.80    (![A:$i,B:$i]:
% 2.53/2.80     ( ( r1_tarski @ A @ B ) <=>
% 2.53/2.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.53/2.80  thf('16', plain,
% 2.53/2.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.80         (~ (r2_hidden @ X0 @ X1)
% 2.53/2.80          | (r2_hidden @ X0 @ X2)
% 2.53/2.80          | ~ (r1_tarski @ X1 @ X2))),
% 2.53/2.80      inference('cnf', [status(esa)], [d3_tarski])).
% 2.53/2.80  thf('17', plain,
% 2.53/2.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.80         ((r2_hidden @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.53/2.80          | ~ (r2_hidden @ X2 @ (k1_zfmisc_1 @ X1)))),
% 2.53/2.80      inference('sup-', [status(thm)], ['15', '16'])).
% 2.53/2.80  thf('18', plain,
% 2.53/2.80      (![X0 : $i]:
% 2.53/2.80         (r2_hidden @ sk_C_1 @ 
% 2.53/2.80          (k1_zfmisc_1 @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)))),
% 2.53/2.80      inference('sup-', [status(thm)], ['12', '17'])).
% 2.53/2.80  thf(t1_subset, axiom,
% 2.53/2.80    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.53/2.80  thf('19', plain,
% 2.53/2.80      (![X22 : $i, X23 : $i]:
% 2.53/2.80         ((m1_subset_1 @ X22 @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 2.53/2.80      inference('cnf', [status(esa)], [t1_subset])).
% 2.53/2.80  thf('20', plain,
% 2.53/2.80      (![X0 : $i]:
% 2.53/2.80         (m1_subset_1 @ sk_C_1 @ 
% 2.53/2.80          (k1_zfmisc_1 @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)))),
% 2.53/2.80      inference('sup-', [status(thm)], ['18', '19'])).
% 2.53/2.80  thf('21', plain,
% 2.53/2.80      (![X0 : $i]:
% 2.53/2.80         (m1_subset_1 @ sk_C_1 @ 
% 2.53/2.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))),
% 2.53/2.80      inference('sup+', [status(thm)], ['7', '20'])).
% 2.53/2.80  thf(cc2_relset_1, axiom,
% 2.53/2.80    (![A:$i,B:$i,C:$i]:
% 2.53/2.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.53/2.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.53/2.80  thf('22', plain,
% 2.53/2.80      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.53/2.80         ((v5_relat_1 @ X35 @ X37)
% 2.53/2.80          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 2.53/2.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.53/2.80  thf('23', plain,
% 2.53/2.80      (![X0 : $i]: (v5_relat_1 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0))),
% 2.53/2.80      inference('sup-', [status(thm)], ['21', '22'])).
% 2.53/2.80  thf('24', plain,
% 2.53/2.80      (![X0 : $i]: (v5_relat_1 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_B))),
% 2.53/2.80      inference('sup+', [status(thm)], ['6', '23'])).
% 2.53/2.80  thf(d19_relat_1, axiom,
% 2.53/2.80    (![A:$i,B:$i]:
% 2.53/2.80     ( ( v1_relat_1 @ B ) =>
% 2.53/2.80       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.53/2.80  thf('25', plain,
% 2.53/2.80      (![X30 : $i, X31 : $i]:
% 2.53/2.80         (~ (v5_relat_1 @ X30 @ X31)
% 2.53/2.80          | (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 2.53/2.80          | ~ (v1_relat_1 @ X30))),
% 2.53/2.80      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.53/2.80  thf('26', plain,
% 2.53/2.80      (![X0 : $i]:
% 2.53/2.80         (~ (v1_relat_1 @ sk_C_1)
% 2.53/2.80          | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ (k2_xboole_0 @ X0 @ sk_B)))),
% 2.53/2.80      inference('sup-', [status(thm)], ['24', '25'])).
% 2.53/2.80  thf('27', plain,
% 2.53/2.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.53/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.80  thf(cc2_relat_1, axiom,
% 2.53/2.80    (![A:$i]:
% 2.53/2.80     ( ( v1_relat_1 @ A ) =>
% 2.53/2.80       ( ![B:$i]:
% 2.53/2.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.53/2.80  thf('28', plain,
% 2.53/2.80      (![X26 : $i, X27 : $i]:
% 2.53/2.80         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 2.53/2.80          | (v1_relat_1 @ X26)
% 2.53/2.80          | ~ (v1_relat_1 @ X27))),
% 2.53/2.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.53/2.80  thf('29', plain,
% 2.53/2.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 2.53/2.80      inference('sup-', [status(thm)], ['27', '28'])).
% 2.53/2.80  thf(fc6_relat_1, axiom,
% 2.53/2.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.53/2.80  thf('30', plain,
% 2.53/2.80      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 2.53/2.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.53/2.80  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 2.53/2.80      inference('demod', [status(thm)], ['29', '30'])).
% 2.53/2.80  thf('32', plain,
% 2.53/2.80      (![X0 : $i]:
% 2.53/2.80         (r1_tarski @ (k2_relat_1 @ sk_C_1) @ (k2_xboole_0 @ X0 @ sk_B))),
% 2.53/2.80      inference('demod', [status(thm)], ['26', '31'])).
% 2.53/2.80  thf('33', plain,
% 2.53/2.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.53/2.80         ((k2_zfmisc_1 @ (k2_xboole_0 @ X15 @ X17) @ X16)
% 2.53/2.80           = (k2_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 2.53/2.80              (k2_zfmisc_1 @ X17 @ X16)))),
% 2.53/2.80      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 2.53/2.80  thf('34', plain,
% 2.53/2.80      (![X0 : $i]:
% 2.53/2.80         (m1_subset_1 @ sk_C_1 @ 
% 2.53/2.80          (k1_zfmisc_1 @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)))),
% 2.53/2.80      inference('sup-', [status(thm)], ['18', '19'])).
% 2.53/2.80  thf('35', plain,
% 2.53/2.80      (![X0 : $i]:
% 2.53/2.80         (m1_subset_1 @ sk_C_1 @ 
% 2.53/2.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)))),
% 2.53/2.80      inference('sup+', [status(thm)], ['33', '34'])).
% 2.53/2.80  thf('36', plain,
% 2.53/2.80      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.53/2.80         ((v4_relat_1 @ X35 @ X36)
% 2.53/2.80          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 2.53/2.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.53/2.80  thf('37', plain,
% 2.53/2.80      (![X0 : $i]: (v4_relat_1 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0))),
% 2.53/2.80      inference('sup-', [status(thm)], ['35', '36'])).
% 2.53/2.80  thf(d18_relat_1, axiom,
% 2.53/2.80    (![A:$i,B:$i]:
% 2.53/2.80     ( ( v1_relat_1 @ B ) =>
% 2.53/2.80       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.53/2.80  thf('38', plain,
% 2.53/2.80      (![X28 : $i, X29 : $i]:
% 2.53/2.80         (~ (v4_relat_1 @ X28 @ X29)
% 2.53/2.80          | (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 2.53/2.80          | ~ (v1_relat_1 @ X28))),
% 2.53/2.80      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.53/2.80  thf('39', plain,
% 2.53/2.80      (![X0 : $i]:
% 2.53/2.80         (~ (v1_relat_1 @ sk_C_1)
% 2.53/2.80          | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.53/2.80      inference('sup-', [status(thm)], ['37', '38'])).
% 2.53/2.80  thf('40', plain, ((v1_relat_1 @ sk_C_1)),
% 2.53/2.80      inference('demod', [status(thm)], ['29', '30'])).
% 2.53/2.80  thf('41', plain,
% 2.53/2.80      (![X0 : $i]:
% 2.53/2.80         (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k2_xboole_0 @ sk_A @ X0))),
% 2.53/2.80      inference('demod', [status(thm)], ['39', '40'])).
% 2.53/2.80  thf(t8_xboole_1, axiom,
% 2.53/2.80    (![A:$i,B:$i,C:$i]:
% 2.53/2.80     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.53/2.80       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.53/2.80  thf('42', plain,
% 2.53/2.80      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.53/2.80         (~ (r1_tarski @ X6 @ X7)
% 2.53/2.80          | ~ (r1_tarski @ X8 @ X7)
% 2.53/2.80          | (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 2.53/2.80      inference('cnf', [status(esa)], [t8_xboole_1])).
% 2.53/2.80  thf('43', plain,
% 2.53/2.80      (![X0 : $i, X1 : $i]:
% 2.53/2.80         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ X1) @ 
% 2.53/2.80           (k2_xboole_0 @ sk_A @ X0))
% 2.53/2.80          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.53/2.80      inference('sup-', [status(thm)], ['41', '42'])).
% 2.53/2.80  thf('44', plain,
% 2.53/2.80      ((r1_tarski @ 
% 2.53/2.80        (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)) @ 
% 2.53/2.80        (k2_xboole_0 @ sk_A @ sk_B))),
% 2.53/2.80      inference('sup-', [status(thm)], ['32', '43'])).
% 2.53/2.80  thf('45', plain,
% 2.53/2.80      (((r1_tarski @ (k3_relat_1 @ sk_C_1) @ (k2_xboole_0 @ sk_A @ sk_B))
% 2.53/2.80        | ~ (v1_relat_1 @ sk_C_1))),
% 2.53/2.80      inference('sup+', [status(thm)], ['1', '44'])).
% 2.53/2.80  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 2.53/2.80      inference('demod', [status(thm)], ['29', '30'])).
% 2.53/2.80  thf('47', plain,
% 2.53/2.80      ((r1_tarski @ (k3_relat_1 @ sk_C_1) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 2.53/2.80      inference('demod', [status(thm)], ['45', '46'])).
% 2.53/2.80  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 2.53/2.80  
% 2.53/2.80  % SZS output end Refutation
% 2.53/2.80  
% 2.53/2.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
