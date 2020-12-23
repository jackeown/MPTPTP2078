%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rZdmGQDOqY

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:50 EST 2020

% Result     : Theorem 8.39s
% Output     : Refutation 8.39s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 114 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  546 ( 795 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X14 ) @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v5_relat_1 @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v5_relat_1 @ X25 @ X27 )
      | ~ ( v5_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc6_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v5_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v5_relat_1 @ X30 @ X31 )
      | ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X2 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v4_relat_1 @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v4_relat_1 @ X22 @ X24 )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( v4_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( v4_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v4_relat_1 @ X28 @ X29 )
      | ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','47'])).

thf('49',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('51',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rZdmGQDOqY
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:45:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.39/8.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.39/8.61  % Solved by: fo/fo7.sh
% 8.39/8.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.39/8.61  % done 11118 iterations in 8.151s
% 8.39/8.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.39/8.61  % SZS output start Refutation
% 8.39/8.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.39/8.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.39/8.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.39/8.61  thf(sk_A_type, type, sk_A: $i).
% 8.39/8.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.39/8.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.39/8.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 8.39/8.61  thf(sk_C_type, type, sk_C: $i).
% 8.39/8.61  thf(sk_B_type, type, sk_B: $i).
% 8.39/8.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.39/8.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.39/8.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.39/8.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.39/8.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.39/8.61  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 8.39/8.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.39/8.61  thf(t19_relset_1, conjecture,
% 8.39/8.61    (![A:$i,B:$i,C:$i]:
% 8.39/8.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.39/8.61       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 8.39/8.61  thf(zf_stmt_0, negated_conjecture,
% 8.39/8.61    (~( ![A:$i,B:$i,C:$i]:
% 8.39/8.61        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.39/8.61          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 8.39/8.61    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 8.39/8.61  thf('0', plain,
% 8.39/8.61      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 8.39/8.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.39/8.61  thf(d6_relat_1, axiom,
% 8.39/8.61    (![A:$i]:
% 8.39/8.61     ( ( v1_relat_1 @ A ) =>
% 8.39/8.61       ( ( k3_relat_1 @ A ) =
% 8.39/8.61         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 8.39/8.61  thf('1', plain,
% 8.39/8.61      (![X32 : $i]:
% 8.39/8.61         (((k3_relat_1 @ X32)
% 8.39/8.61            = (k2_xboole_0 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32)))
% 8.39/8.61          | ~ (v1_relat_1 @ X32))),
% 8.39/8.61      inference('cnf', [status(esa)], [d6_relat_1])).
% 8.39/8.61  thf(commutativity_k2_tarski, axiom,
% 8.39/8.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 8.39/8.61  thf('2', plain,
% 8.39/8.61      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 8.39/8.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.39/8.61  thf(l51_zfmisc_1, axiom,
% 8.39/8.61    (![A:$i,B:$i]:
% 8.39/8.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.39/8.61  thf('3', plain,
% 8.39/8.61      (![X12 : $i, X13 : $i]:
% 8.39/8.61         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 8.39/8.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.39/8.61  thf('4', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i]:
% 8.39/8.61         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 8.39/8.61      inference('sup+', [status(thm)], ['2', '3'])).
% 8.39/8.61  thf('5', plain,
% 8.39/8.61      (![X12 : $i, X13 : $i]:
% 8.39/8.61         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 8.39/8.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.39/8.61  thf('6', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.39/8.61      inference('sup+', [status(thm)], ['4', '5'])).
% 8.39/8.61  thf(t7_xboole_1, axiom,
% 8.39/8.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 8.39/8.61  thf('7', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 8.39/8.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.39/8.61  thf(t118_zfmisc_1, axiom,
% 8.39/8.61    (![A:$i,B:$i,C:$i]:
% 8.39/8.61     ( ( r1_tarski @ A @ B ) =>
% 8.39/8.61       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 8.39/8.61         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 8.39/8.61  thf('8', plain,
% 8.39/8.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.39/8.61         (~ (r1_tarski @ X14 @ X15)
% 8.39/8.61          | (r1_tarski @ (k2_zfmisc_1 @ X16 @ X14) @ (k2_zfmisc_1 @ X16 @ X15)))),
% 8.39/8.61      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 8.39/8.61  thf('9', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.39/8.61         (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 8.39/8.61          (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.39/8.61      inference('sup-', [status(thm)], ['7', '8'])).
% 8.39/8.61  thf(t3_subset, axiom,
% 8.39/8.61    (![A:$i,B:$i]:
% 8.39/8.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.39/8.61  thf('10', plain,
% 8.39/8.61      (![X17 : $i, X19 : $i]:
% 8.39/8.61         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 8.39/8.61      inference('cnf', [status(esa)], [t3_subset])).
% 8.39/8.61  thf('11', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.39/8.61         (m1_subset_1 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 8.39/8.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 8.39/8.61      inference('sup-', [status(thm)], ['9', '10'])).
% 8.39/8.61  thf(cc2_relset_1, axiom,
% 8.39/8.61    (![A:$i,B:$i,C:$i]:
% 8.39/8.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.39/8.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.39/8.61  thf('12', plain,
% 8.39/8.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 8.39/8.61         ((v5_relat_1 @ X35 @ X37)
% 8.39/8.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 8.39/8.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.39/8.61  thf('13', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.39/8.61         (v5_relat_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 8.39/8.61      inference('sup-', [status(thm)], ['11', '12'])).
% 8.39/8.61  thf('14', plain,
% 8.39/8.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.39/8.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.39/8.61  thf(cc6_relat_1, axiom,
% 8.39/8.61    (![A:$i,B:$i]:
% 8.39/8.61     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 8.39/8.61       ( ![C:$i]:
% 8.39/8.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v5_relat_1 @ C @ A ) ) ) ))).
% 8.39/8.61  thf('15', plain,
% 8.39/8.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 8.39/8.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 8.39/8.61          | (v5_relat_1 @ X25 @ X27)
% 8.39/8.61          | ~ (v5_relat_1 @ X26 @ X27)
% 8.39/8.61          | ~ (v1_relat_1 @ X26))),
% 8.39/8.61      inference('cnf', [status(esa)], [cc6_relat_1])).
% 8.39/8.61  thf('16', plain,
% 8.39/8.61      (![X0 : $i]:
% 8.39/8.61         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 8.39/8.61          | ~ (v5_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 8.39/8.61          | (v5_relat_1 @ sk_C @ X0))),
% 8.39/8.61      inference('sup-', [status(thm)], ['14', '15'])).
% 8.39/8.61  thf(fc6_relat_1, axiom,
% 8.39/8.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.39/8.61  thf('17', plain,
% 8.39/8.61      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 8.39/8.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.39/8.61  thf('18', plain,
% 8.39/8.61      (![X0 : $i]:
% 8.39/8.61         (~ (v5_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 8.39/8.61          | (v5_relat_1 @ sk_C @ X0))),
% 8.39/8.61      inference('demod', [status(thm)], ['16', '17'])).
% 8.39/8.61  thf('19', plain,
% 8.39/8.61      (![X0 : $i]: (v5_relat_1 @ sk_C @ (k2_xboole_0 @ sk_B @ X0))),
% 8.39/8.61      inference('sup-', [status(thm)], ['13', '18'])).
% 8.39/8.61  thf('20', plain,
% 8.39/8.61      (![X0 : $i]: (v5_relat_1 @ sk_C @ (k2_xboole_0 @ X0 @ sk_B))),
% 8.39/8.61      inference('sup+', [status(thm)], ['6', '19'])).
% 8.39/8.61  thf(d19_relat_1, axiom,
% 8.39/8.61    (![A:$i,B:$i]:
% 8.39/8.61     ( ( v1_relat_1 @ B ) =>
% 8.39/8.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 8.39/8.61  thf('21', plain,
% 8.39/8.61      (![X30 : $i, X31 : $i]:
% 8.39/8.61         (~ (v5_relat_1 @ X30 @ X31)
% 8.39/8.61          | (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 8.39/8.61          | ~ (v1_relat_1 @ X30))),
% 8.39/8.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.39/8.61  thf('22', plain,
% 8.39/8.61      (![X0 : $i]:
% 8.39/8.61         (~ (v1_relat_1 @ sk_C)
% 8.39/8.61          | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B)))),
% 8.39/8.61      inference('sup-', [status(thm)], ['20', '21'])).
% 8.39/8.61  thf('23', plain,
% 8.39/8.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.39/8.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.39/8.61  thf(cc2_relat_1, axiom,
% 8.39/8.61    (![A:$i]:
% 8.39/8.61     ( ( v1_relat_1 @ A ) =>
% 8.39/8.61       ( ![B:$i]:
% 8.39/8.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.39/8.61  thf('24', plain,
% 8.39/8.61      (![X20 : $i, X21 : $i]:
% 8.39/8.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 8.39/8.61          | (v1_relat_1 @ X20)
% 8.39/8.61          | ~ (v1_relat_1 @ X21))),
% 8.39/8.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.39/8.61  thf('25', plain,
% 8.39/8.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 8.39/8.61      inference('sup-', [status(thm)], ['23', '24'])).
% 8.39/8.61  thf('26', plain,
% 8.39/8.61      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 8.39/8.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.39/8.61  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 8.39/8.61      inference('demod', [status(thm)], ['25', '26'])).
% 8.39/8.61  thf('28', plain,
% 8.39/8.61      (![X0 : $i]:
% 8.39/8.61         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 8.39/8.61      inference('demod', [status(thm)], ['22', '27'])).
% 8.39/8.61  thf('29', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 8.39/8.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.39/8.61  thf('30', plain,
% 8.39/8.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.39/8.61         (~ (r1_tarski @ X14 @ X15)
% 8.39/8.61          | (r1_tarski @ (k2_zfmisc_1 @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X16)))),
% 8.39/8.61      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 8.39/8.61  thf('31', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.39/8.61         (r1_tarski @ (k2_zfmisc_1 @ X1 @ X2) @ 
% 8.39/8.61          (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 8.39/8.61      inference('sup-', [status(thm)], ['29', '30'])).
% 8.39/8.61  thf('32', plain,
% 8.39/8.61      (![X17 : $i, X19 : $i]:
% 8.39/8.61         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 8.39/8.61      inference('cnf', [status(esa)], [t3_subset])).
% 8.39/8.61  thf('33', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.39/8.61         (m1_subset_1 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 8.39/8.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 8.39/8.61      inference('sup-', [status(thm)], ['31', '32'])).
% 8.39/8.61  thf('34', plain,
% 8.39/8.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 8.39/8.61         ((v4_relat_1 @ X35 @ X36)
% 8.39/8.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 8.39/8.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.39/8.61  thf('35', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.39/8.61         (v4_relat_1 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_xboole_0 @ X2 @ X1))),
% 8.39/8.61      inference('sup-', [status(thm)], ['33', '34'])).
% 8.39/8.61  thf('36', plain,
% 8.39/8.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.39/8.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.39/8.61  thf(cc5_relat_1, axiom,
% 8.39/8.61    (![A:$i,B:$i]:
% 8.39/8.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 8.39/8.61       ( ![C:$i]:
% 8.39/8.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v4_relat_1 @ C @ A ) ) ) ))).
% 8.39/8.61  thf('37', plain,
% 8.39/8.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 8.39/8.61         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 8.39/8.61          | (v4_relat_1 @ X22 @ X24)
% 8.39/8.61          | ~ (v4_relat_1 @ X23 @ X24)
% 8.39/8.61          | ~ (v1_relat_1 @ X23))),
% 8.39/8.61      inference('cnf', [status(esa)], [cc5_relat_1])).
% 8.39/8.61  thf('38', plain,
% 8.39/8.61      (![X0 : $i]:
% 8.39/8.61         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 8.39/8.61          | ~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 8.39/8.61          | (v4_relat_1 @ sk_C @ X0))),
% 8.39/8.61      inference('sup-', [status(thm)], ['36', '37'])).
% 8.39/8.61  thf('39', plain,
% 8.39/8.61      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 8.39/8.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.39/8.61  thf('40', plain,
% 8.39/8.61      (![X0 : $i]:
% 8.39/8.61         (~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 8.39/8.61          | (v4_relat_1 @ sk_C @ X0))),
% 8.39/8.61      inference('demod', [status(thm)], ['38', '39'])).
% 8.39/8.61  thf('41', plain,
% 8.39/8.61      (![X0 : $i]: (v4_relat_1 @ sk_C @ (k2_xboole_0 @ sk_A @ X0))),
% 8.39/8.61      inference('sup-', [status(thm)], ['35', '40'])).
% 8.39/8.61  thf(d18_relat_1, axiom,
% 8.39/8.61    (![A:$i,B:$i]:
% 8.39/8.61     ( ( v1_relat_1 @ B ) =>
% 8.39/8.61       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 8.39/8.61  thf('42', plain,
% 8.39/8.61      (![X28 : $i, X29 : $i]:
% 8.39/8.61         (~ (v4_relat_1 @ X28 @ X29)
% 8.39/8.61          | (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 8.39/8.61          | ~ (v1_relat_1 @ X28))),
% 8.39/8.61      inference('cnf', [status(esa)], [d18_relat_1])).
% 8.39/8.61  thf('43', plain,
% 8.39/8.61      (![X0 : $i]:
% 8.39/8.61         (~ (v1_relat_1 @ sk_C)
% 8.39/8.61          | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0)))),
% 8.39/8.61      inference('sup-', [status(thm)], ['41', '42'])).
% 8.39/8.61  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 8.39/8.61      inference('demod', [status(thm)], ['25', '26'])).
% 8.39/8.61  thf('45', plain,
% 8.39/8.61      (![X0 : $i]:
% 8.39/8.61         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ X0))),
% 8.39/8.61      inference('demod', [status(thm)], ['43', '44'])).
% 8.39/8.61  thf(t8_xboole_1, axiom,
% 8.39/8.61    (![A:$i,B:$i,C:$i]:
% 8.39/8.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 8.39/8.61       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 8.39/8.61  thf('46', plain,
% 8.39/8.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 8.39/8.61         (~ (r1_tarski @ X2 @ X3)
% 8.39/8.61          | ~ (r1_tarski @ X4 @ X3)
% 8.39/8.61          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 8.39/8.61      inference('cnf', [status(esa)], [t8_xboole_1])).
% 8.39/8.61  thf('47', plain,
% 8.39/8.61      (![X0 : $i, X1 : $i]:
% 8.39/8.61         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 8.39/8.61           (k2_xboole_0 @ sk_A @ X0))
% 8.39/8.61          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_A @ X0)))),
% 8.39/8.61      inference('sup-', [status(thm)], ['45', '46'])).
% 8.39/8.61  thf('48', plain,
% 8.39/8.61      ((r1_tarski @ 
% 8.39/8.61        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 8.39/8.61        (k2_xboole_0 @ sk_A @ sk_B))),
% 8.39/8.61      inference('sup-', [status(thm)], ['28', '47'])).
% 8.39/8.61  thf('49', plain,
% 8.39/8.61      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 8.39/8.61        | ~ (v1_relat_1 @ sk_C))),
% 8.39/8.61      inference('sup+', [status(thm)], ['1', '48'])).
% 8.39/8.61  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 8.39/8.61      inference('demod', [status(thm)], ['25', '26'])).
% 8.39/8.61  thf('51', plain,
% 8.39/8.61      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 8.39/8.61      inference('demod', [status(thm)], ['49', '50'])).
% 8.39/8.61  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 8.39/8.61  
% 8.39/8.61  % SZS output end Refutation
% 8.39/8.61  
% 8.39/8.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
