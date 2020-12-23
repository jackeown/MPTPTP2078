%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZUI4wkeHZa

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:52 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 124 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   18
%              Number of atoms          :  506 ( 885 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X24: $i] :
      ( ( ( k3_relat_1 @ X24 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X24 ) @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ X16 @ ( k2_xboole_0 @ X13 @ X15 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X13 ) @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v5_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27
        = ( k7_relat_1 @ X27 @ X28 ) )
      | ~ ( v4_relat_1 @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( sk_C
        = ( k7_relat_1 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('35',plain,(
    ! [X0: $i] :
      ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('47',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZUI4wkeHZa
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.89/2.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.89/2.09  % Solved by: fo/fo7.sh
% 1.89/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.89/2.09  % done 2071 iterations in 1.657s
% 1.89/2.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.89/2.09  % SZS output start Refutation
% 1.89/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.89/2.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.89/2.09  thf(sk_B_type, type, sk_B: $i).
% 1.89/2.09  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.89/2.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.89/2.09  thf(sk_C_type, type, sk_C: $i).
% 1.89/2.09  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.89/2.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.89/2.09  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.89/2.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.89/2.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.89/2.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.89/2.09  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.89/2.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.89/2.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.89/2.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.89/2.09  thf(t19_relset_1, conjecture,
% 1.89/2.09    (![A:$i,B:$i,C:$i]:
% 1.89/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.89/2.09       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.89/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.89/2.09    (~( ![A:$i,B:$i,C:$i]:
% 1.89/2.09        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.89/2.09          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.89/2.09    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 1.89/2.09  thf('0', plain,
% 1.89/2.09      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf(d6_relat_1, axiom,
% 1.89/2.09    (![A:$i]:
% 1.89/2.09     ( ( v1_relat_1 @ A ) =>
% 1.89/2.09       ( ( k3_relat_1 @ A ) =
% 1.89/2.09         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.89/2.09  thf('1', plain,
% 1.89/2.09      (![X24 : $i]:
% 1.89/2.09         (((k3_relat_1 @ X24)
% 1.89/2.09            = (k2_xboole_0 @ (k1_relat_1 @ X24) @ (k2_relat_1 @ X24)))
% 1.89/2.09          | ~ (v1_relat_1 @ X24))),
% 1.89/2.09      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.89/2.09  thf(t120_zfmisc_1, axiom,
% 1.89/2.09    (![A:$i,B:$i,C:$i]:
% 1.89/2.09     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.89/2.09         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.89/2.09       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.89/2.09         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.89/2.09  thf('2', plain,
% 1.89/2.09      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.89/2.09         ((k2_zfmisc_1 @ X16 @ (k2_xboole_0 @ X13 @ X15))
% 1.89/2.09           = (k2_xboole_0 @ (k2_zfmisc_1 @ X16 @ X13) @ 
% 1.89/2.09              (k2_zfmisc_1 @ X16 @ X15)))),
% 1.89/2.09      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.89/2.09  thf(commutativity_k2_xboole_0, axiom,
% 1.89/2.09    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.89/2.09  thf('3', plain,
% 1.89/2.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.89/2.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.89/2.09  thf('4', plain,
% 1.89/2.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.89/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.09  thf(t3_subset, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.90/2.09  thf('5', plain,
% 1.90/2.09      (![X17 : $i, X18 : $i]:
% 1.90/2.09         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.90/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.90/2.09  thf('6', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.90/2.09      inference('sup-', [status(thm)], ['4', '5'])).
% 1.90/2.09  thf(t109_xboole_1, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 1.90/2.09  thf('7', plain,
% 1.90/2.09      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.90/2.09         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 1.90/2.09      inference('cnf', [status(esa)], [t109_xboole_1])).
% 1.90/2.09  thf('8', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.90/2.09      inference('sup-', [status(thm)], ['6', '7'])).
% 1.90/2.09  thf(t44_xboole_1, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.90/2.09       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.90/2.09  thf('9', plain,
% 1.90/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.90/2.09         ((r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 1.90/2.09          | ~ (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7))),
% 1.90/2.09      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.90/2.09  thf('10', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ sk_C @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['8', '9'])).
% 1.90/2.09  thf('11', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ sk_C @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 1.90/2.09      inference('sup+', [status(thm)], ['3', '10'])).
% 1.90/2.09  thf('12', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.90/2.09      inference('sup+', [status(thm)], ['2', '11'])).
% 1.90/2.09  thf('13', plain,
% 1.90/2.09      (![X17 : $i, X19 : $i]:
% 1.90/2.09         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 1.90/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.90/2.09  thf('14', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (m1_subset_1 @ sk_C @ 
% 1.90/2.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['12', '13'])).
% 1.90/2.09  thf(cc2_relset_1, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.90/2.09       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.90/2.09  thf('15', plain,
% 1.90/2.09      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.90/2.09         ((v5_relat_1 @ X31 @ X33)
% 1.90/2.09          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.90/2.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.90/2.09  thf('16', plain,
% 1.90/2.09      (![X0 : $i]: (v5_relat_1 @ sk_C @ (k2_xboole_0 @ sk_B @ X0))),
% 1.90/2.09      inference('sup-', [status(thm)], ['14', '15'])).
% 1.90/2.09  thf(d19_relat_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( v1_relat_1 @ B ) =>
% 1.90/2.09       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.90/2.09  thf('17', plain,
% 1.90/2.09      (![X22 : $i, X23 : $i]:
% 1.90/2.09         (~ (v5_relat_1 @ X22 @ X23)
% 1.90/2.09          | (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 1.90/2.09          | ~ (v1_relat_1 @ X22))),
% 1.90/2.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.90/2.09  thf('18', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (~ (v1_relat_1 @ sk_C)
% 1.90/2.09          | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['16', '17'])).
% 1.90/2.09  thf('19', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf(cc2_relat_1, axiom,
% 1.90/2.09    (![A:$i]:
% 1.90/2.09     ( ( v1_relat_1 @ A ) =>
% 1.90/2.09       ( ![B:$i]:
% 1.90/2.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.90/2.09  thf('20', plain,
% 1.90/2.09      (![X20 : $i, X21 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.90/2.09          | (v1_relat_1 @ X20)
% 1.90/2.09          | ~ (v1_relat_1 @ X21))),
% 1.90/2.09      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.90/2.09  thf('21', plain,
% 1.90/2.09      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.90/2.09      inference('sup-', [status(thm)], ['19', '20'])).
% 1.90/2.09  thf(fc6_relat_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.90/2.09  thf('22', plain,
% 1.90/2.09      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 1.90/2.09      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.90/2.09  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 1.90/2.09      inference('demod', [status(thm)], ['21', '22'])).
% 1.90/2.09  thf('24', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))),
% 1.90/2.09      inference('demod', [status(thm)], ['18', '23'])).
% 1.90/2.09  thf('25', plain,
% 1.90/2.09      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.90/2.09         ((k2_zfmisc_1 @ (k2_xboole_0 @ X13 @ X15) @ X14)
% 1.90/2.09           = (k2_xboole_0 @ (k2_zfmisc_1 @ X13 @ X14) @ 
% 1.90/2.09              (k2_zfmisc_1 @ X15 @ X14)))),
% 1.90/2.09      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.90/2.09  thf('26', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ sk_C @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['8', '9'])).
% 1.90/2.09  thf('27', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ sk_C @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 1.90/2.09      inference('sup+', [status(thm)], ['25', '26'])).
% 1.90/2.09  thf('28', plain,
% 1.90/2.09      (![X17 : $i, X19 : $i]:
% 1.90/2.09         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 1.90/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.90/2.09  thf('29', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (m1_subset_1 @ sk_C @ 
% 1.90/2.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['27', '28'])).
% 1.90/2.09  thf('30', plain,
% 1.90/2.09      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.90/2.09         ((v4_relat_1 @ X31 @ X32)
% 1.90/2.09          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.90/2.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.90/2.09  thf('31', plain,
% 1.90/2.09      (![X0 : $i]: (v4_relat_1 @ sk_C @ (k2_xboole_0 @ X0 @ sk_A))),
% 1.90/2.09      inference('sup-', [status(thm)], ['29', '30'])).
% 1.90/2.09  thf(t209_relat_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.90/2.09       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.90/2.09  thf('32', plain,
% 1.90/2.09      (![X27 : $i, X28 : $i]:
% 1.90/2.09         (((X27) = (k7_relat_1 @ X27 @ X28))
% 1.90/2.09          | ~ (v4_relat_1 @ X27 @ X28)
% 1.90/2.09          | ~ (v1_relat_1 @ X27))),
% 1.90/2.09      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.90/2.09  thf('33', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (~ (v1_relat_1 @ sk_C)
% 1.90/2.09          | ((sk_C) = (k7_relat_1 @ sk_C @ (k2_xboole_0 @ X0 @ sk_A))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['31', '32'])).
% 1.90/2.09  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 1.90/2.09      inference('demod', [status(thm)], ['21', '22'])).
% 1.90/2.09  thf('35', plain,
% 1.90/2.09      (![X0 : $i]: ((sk_C) = (k7_relat_1 @ sk_C @ (k2_xboole_0 @ X0 @ sk_A)))),
% 1.90/2.09      inference('demod', [status(thm)], ['33', '34'])).
% 1.90/2.09  thf(t87_relat_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( v1_relat_1 @ B ) =>
% 1.90/2.09       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.90/2.09  thf('36', plain,
% 1.90/2.09      (![X29 : $i, X30 : $i]:
% 1.90/2.09         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X29 @ X30)) @ X30)
% 1.90/2.09          | ~ (v1_relat_1 @ X29))),
% 1.90/2.09      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.90/2.09  thf('37', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))
% 1.90/2.09          | ~ (v1_relat_1 @ sk_C))),
% 1.90/2.09      inference('sup+', [status(thm)], ['35', '36'])).
% 1.90/2.09  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 1.90/2.09      inference('demod', [status(thm)], ['21', '22'])).
% 1.90/2.09  thf('39', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 1.90/2.09      inference('demod', [status(thm)], ['37', '38'])).
% 1.90/2.09  thf(t8_xboole_1, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.90/2.09       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.90/2.09  thf('40', plain,
% 1.90/2.09      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.90/2.09         (~ (r1_tarski @ X8 @ X9)
% 1.90/2.09          | ~ (r1_tarski @ X10 @ X9)
% 1.90/2.09          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.90/2.09      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.90/2.09  thf('41', plain,
% 1.90/2.09      (![X0 : $i, X1 : $i]:
% 1.90/2.09         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 1.90/2.09           (k2_xboole_0 @ X0 @ sk_A))
% 1.90/2.09          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_A)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['39', '40'])).
% 1.90/2.09  thf('42', plain,
% 1.90/2.09      ((r1_tarski @ 
% 1.90/2.09        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 1.90/2.09        (k2_xboole_0 @ sk_B @ sk_A))),
% 1.90/2.09      inference('sup-', [status(thm)], ['24', '41'])).
% 1.90/2.09  thf('43', plain,
% 1.90/2.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.90/2.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.90/2.09  thf('44', plain,
% 1.90/2.09      ((r1_tarski @ 
% 1.90/2.09        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 1.90/2.09        (k2_xboole_0 @ sk_A @ sk_B))),
% 1.90/2.09      inference('demod', [status(thm)], ['42', '43'])).
% 1.90/2.09  thf('45', plain,
% 1.90/2.09      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 1.90/2.09        | ~ (v1_relat_1 @ sk_C))),
% 1.90/2.09      inference('sup+', [status(thm)], ['1', '44'])).
% 1.90/2.09  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 1.90/2.09      inference('demod', [status(thm)], ['21', '22'])).
% 1.90/2.09  thf('47', plain,
% 1.90/2.09      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 1.90/2.09      inference('demod', [status(thm)], ['45', '46'])).
% 1.90/2.09  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 1.90/2.09  
% 1.90/2.09  % SZS output end Refutation
% 1.90/2.09  
% 1.90/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
