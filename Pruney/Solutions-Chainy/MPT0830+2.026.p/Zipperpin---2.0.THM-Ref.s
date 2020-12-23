%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AdaGL1nBm8

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:17 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 150 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  569 (1239 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t33_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k5_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k7_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) @ X9 )
      | ~ ( v4_relat_1 @ X8 @ X10 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X10 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v4_relat_1 @ X1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1
        = ( k7_relat_1 @ X1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k7_relat_1 @ X1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_D @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('37',plain,(
    ! [X0: $i] :
      ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t107_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k2_xboole_0 @ ( k7_relat_1 @ X16 @ X17 ) @ ( k7_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t107_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X2 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('47',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r1_tarski @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['4','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AdaGL1nBm8
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.27/1.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.27/1.48  % Solved by: fo/fo7.sh
% 1.27/1.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.48  % done 2210 iterations in 1.038s
% 1.27/1.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.27/1.48  % SZS output start Refutation
% 1.27/1.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.27/1.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.27/1.48  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.27/1.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.27/1.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.27/1.48  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.48  thf(sk_C_type, type, sk_C: $i).
% 1.27/1.48  thf(sk_D_type, type, sk_D: $i).
% 1.27/1.48  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 1.27/1.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.27/1.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.27/1.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.27/1.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.27/1.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.27/1.48  thf(t33_relset_1, conjecture,
% 1.27/1.48    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.27/1.48       ( m1_subset_1 @
% 1.27/1.48         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.27/1.48         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.27/1.48  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.48        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.27/1.48          ( m1_subset_1 @
% 1.27/1.48            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.27/1.48            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 1.27/1.48    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 1.27/1.48  thf('0', plain,
% 1.27/1.48      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 1.27/1.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('1', plain,
% 1.27/1.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf(redefinition_k5_relset_1, axiom,
% 1.27/1.48    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.27/1.48       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.27/1.48  thf('2', plain,
% 1.27/1.48      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.27/1.48         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.27/1.48          | ((k5_relset_1 @ X25 @ X26 @ X24 @ X27) = (k7_relat_1 @ X24 @ X27)))),
% 1.27/1.48      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 1.27/1.48  thf('3', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.27/1.48      inference('sup-', [status(thm)], ['1', '2'])).
% 1.27/1.48  thf('4', plain,
% 1.27/1.48      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 1.27/1.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.27/1.48      inference('demod', [status(thm)], ['0', '3'])).
% 1.27/1.48  thf('5', plain,
% 1.27/1.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf(cc2_relset_1, axiom,
% 1.27/1.48    (![A:$i,B:$i,C:$i]:
% 1.27/1.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.27/1.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.27/1.48  thf('6', plain,
% 1.27/1.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.27/1.48         ((v4_relat_1 @ X21 @ X22)
% 1.27/1.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.27/1.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.27/1.48  thf('7', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.27/1.48      inference('sup-', [status(thm)], ['5', '6'])).
% 1.27/1.48  thf(fc23_relat_1, axiom,
% 1.27/1.48    (![A:$i,B:$i,C:$i]:
% 1.27/1.48     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 1.27/1.48       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 1.27/1.48         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 1.27/1.48         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 1.27/1.48  thf('8', plain,
% 1.27/1.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.27/1.48         ((v4_relat_1 @ (k7_relat_1 @ X8 @ X9) @ X9)
% 1.27/1.48          | ~ (v4_relat_1 @ X8 @ X10)
% 1.27/1.48          | ~ (v1_relat_1 @ X8))),
% 1.27/1.48      inference('cnf', [status(esa)], [fc23_relat_1])).
% 1.27/1.48  thf('9', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 1.27/1.48      inference('sup-', [status(thm)], ['7', '8'])).
% 1.27/1.48  thf('10', plain,
% 1.27/1.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf(cc2_relat_1, axiom,
% 1.27/1.48    (![A:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ A ) =>
% 1.27/1.48       ( ![B:$i]:
% 1.27/1.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.27/1.48  thf('11', plain,
% 1.27/1.48      (![X4 : $i, X5 : $i]:
% 1.27/1.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.27/1.48          | (v1_relat_1 @ X4)
% 1.27/1.48          | ~ (v1_relat_1 @ X5))),
% 1.27/1.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.27/1.48  thf('12', plain,
% 1.27/1.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D))),
% 1.27/1.48      inference('sup-', [status(thm)], ['10', '11'])).
% 1.27/1.48  thf(fc6_relat_1, axiom,
% 1.27/1.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.27/1.48  thf('13', plain,
% 1.27/1.48      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 1.27/1.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.27/1.48  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.48      inference('demod', [status(thm)], ['12', '13'])).
% 1.27/1.48  thf('15', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 1.27/1.48      inference('demod', [status(thm)], ['9', '14'])).
% 1.27/1.48  thf(d18_relat_1, axiom,
% 1.27/1.48    (![A:$i,B:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ B ) =>
% 1.27/1.48       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.27/1.48  thf('16', plain,
% 1.27/1.48      (![X6 : $i, X7 : $i]:
% 1.27/1.48         (~ (v4_relat_1 @ X6 @ X7)
% 1.27/1.48          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 1.27/1.48          | ~ (v1_relat_1 @ X6))),
% 1.27/1.48      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.27/1.48  thf('17', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 1.27/1.48          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 1.27/1.48      inference('sup-', [status(thm)], ['15', '16'])).
% 1.27/1.48  thf('18', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.27/1.48      inference('sup-', [status(thm)], ['5', '6'])).
% 1.27/1.48  thf('19', plain,
% 1.27/1.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.27/1.48         ((v1_relat_1 @ (k7_relat_1 @ X8 @ X9))
% 1.27/1.48          | ~ (v4_relat_1 @ X8 @ X10)
% 1.27/1.48          | ~ (v1_relat_1 @ X8))),
% 1.27/1.48      inference('cnf', [status(esa)], [fc23_relat_1])).
% 1.27/1.48  thf('20', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['18', '19'])).
% 1.27/1.48  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.48      inference('demod', [status(thm)], ['12', '13'])).
% 1.27/1.48  thf('22', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 1.27/1.48      inference('demod', [status(thm)], ['20', '21'])).
% 1.27/1.48  thf('23', plain,
% 1.27/1.48      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 1.27/1.48      inference('demod', [status(thm)], ['17', '22'])).
% 1.27/1.48  thf(t7_xboole_1, axiom,
% 1.27/1.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.27/1.48  thf('24', plain,
% 1.27/1.48      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 1.27/1.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.27/1.48  thf('25', plain,
% 1.27/1.48      (![X6 : $i, X7 : $i]:
% 1.27/1.48         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 1.27/1.48          | (v4_relat_1 @ X6 @ X7)
% 1.27/1.48          | ~ (v1_relat_1 @ X6))),
% 1.27/1.48      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.27/1.48  thf('26', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X1)
% 1.27/1.48          | (v4_relat_1 @ X1 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['24', '25'])).
% 1.27/1.48  thf(t209_relat_1, axiom,
% 1.27/1.48    (![A:$i,B:$i]:
% 1.27/1.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.27/1.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.27/1.48  thf('27', plain,
% 1.27/1.48      (![X19 : $i, X20 : $i]:
% 1.27/1.48         (((X19) = (k7_relat_1 @ X19 @ X20))
% 1.27/1.48          | ~ (v4_relat_1 @ X19 @ X20)
% 1.27/1.48          | ~ (v1_relat_1 @ X19))),
% 1.27/1.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.27/1.48  thf('28', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X1)
% 1.27/1.48          | ~ (v1_relat_1 @ X1)
% 1.27/1.48          | ((X1) = (k7_relat_1 @ X1 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 1.27/1.48      inference('sup-', [status(thm)], ['26', '27'])).
% 1.27/1.48  thf('29', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]:
% 1.27/1.48         (((X1) = (k7_relat_1 @ X1 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 1.27/1.48          | ~ (v1_relat_1 @ X1))),
% 1.27/1.48      inference('simplify', [status(thm)], ['28'])).
% 1.27/1.48  thf('30', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 1.27/1.48      inference('demod', [status(thm)], ['9', '14'])).
% 1.27/1.48  thf('31', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((v4_relat_1 @ sk_D @ (k2_xboole_0 @ (k1_relat_1 @ sk_D) @ X0))
% 1.27/1.48          | ~ (v1_relat_1 @ sk_D))),
% 1.27/1.48      inference('sup+', [status(thm)], ['29', '30'])).
% 1.27/1.48  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.48      inference('demod', [status(thm)], ['12', '13'])).
% 1.27/1.48  thf('33', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (v4_relat_1 @ sk_D @ (k2_xboole_0 @ (k1_relat_1 @ sk_D) @ X0))),
% 1.27/1.48      inference('demod', [status(thm)], ['31', '32'])).
% 1.27/1.48  thf('34', plain,
% 1.27/1.48      (![X19 : $i, X20 : $i]:
% 1.27/1.48         (((X19) = (k7_relat_1 @ X19 @ X20))
% 1.27/1.48          | ~ (v4_relat_1 @ X19 @ X20)
% 1.27/1.48          | ~ (v1_relat_1 @ X19))),
% 1.27/1.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.27/1.48  thf('35', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ sk_D)
% 1.27/1.48          | ((sk_D)
% 1.27/1.48              = (k7_relat_1 @ sk_D @ (k2_xboole_0 @ (k1_relat_1 @ sk_D) @ X0))))),
% 1.27/1.48      inference('sup-', [status(thm)], ['33', '34'])).
% 1.27/1.48  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.48      inference('demod', [status(thm)], ['12', '13'])).
% 1.27/1.48  thf('37', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((sk_D)
% 1.27/1.48           = (k7_relat_1 @ sk_D @ (k2_xboole_0 @ (k1_relat_1 @ sk_D) @ X0)))),
% 1.27/1.48      inference('demod', [status(thm)], ['35', '36'])).
% 1.27/1.48  thf(t107_relat_1, axiom,
% 1.27/1.48    (![A:$i,B:$i,C:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ C ) =>
% 1.27/1.48       ( ( k7_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.27/1.48         ( k2_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 1.27/1.48  thf('38', plain,
% 1.27/1.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.27/1.48         (((k7_relat_1 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.27/1.48            = (k2_xboole_0 @ (k7_relat_1 @ X16 @ X17) @ 
% 1.27/1.48               (k7_relat_1 @ X16 @ X18)))
% 1.27/1.48          | ~ (v1_relat_1 @ X16))),
% 1.27/1.48      inference('cnf', [status(esa)], [t107_relat_1])).
% 1.27/1.48  thf(commutativity_k2_xboole_0, axiom,
% 1.27/1.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.27/1.48  thf('39', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.27/1.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.27/1.48  thf('40', plain,
% 1.27/1.48      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 1.27/1.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.27/1.48  thf('41', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.27/1.48      inference('sup+', [status(thm)], ['39', '40'])).
% 1.27/1.48  thf('42', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         ((r1_tarski @ (k7_relat_1 @ X2 @ X0) @ 
% 1.27/1.48           (k7_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.27/1.48          | ~ (v1_relat_1 @ X2))),
% 1.27/1.48      inference('sup+', [status(thm)], ['38', '41'])).
% 1.27/1.48  thf('43', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 1.27/1.48      inference('sup+', [status(thm)], ['37', '42'])).
% 1.27/1.48  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.48      inference('demod', [status(thm)], ['12', '13'])).
% 1.27/1.48  thf('45', plain, (![X0 : $i]: (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D)),
% 1.27/1.48      inference('demod', [status(thm)], ['43', '44'])).
% 1.27/1.48  thf('46', plain,
% 1.27/1.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf(t4_relset_1, axiom,
% 1.27/1.48    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 1.27/1.48       ( ( r1_tarski @ A @ D ) =>
% 1.27/1.48         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.27/1.48  thf('47', plain,
% 1.27/1.48      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.27/1.48         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.27/1.48          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.27/1.48          | ~ (r1_tarski @ X32 @ X35))),
% 1.27/1.48      inference('cnf', [status(esa)], [t4_relset_1])).
% 1.27/1.48  thf('48', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (r1_tarski @ X0 @ sk_D)
% 1.27/1.48          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.27/1.48      inference('sup-', [status(thm)], ['46', '47'])).
% 1.27/1.48  thf('49', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.27/1.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['45', '48'])).
% 1.27/1.48  thf(t13_relset_1, axiom,
% 1.27/1.48    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.27/1.48       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 1.27/1.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.27/1.48  thf('50', plain,
% 1.27/1.48      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.27/1.48         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 1.27/1.48          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.27/1.48          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 1.27/1.48      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.27/1.48  thf('51', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]:
% 1.27/1.48         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.27/1.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 1.27/1.48          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 1.27/1.48      inference('sup-', [status(thm)], ['49', '50'])).
% 1.27/1.48  thf('52', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.27/1.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['23', '51'])).
% 1.27/1.48  thf('53', plain, ($false), inference('demod', [status(thm)], ['4', '52'])).
% 1.27/1.48  
% 1.27/1.48  % SZS output end Refutation
% 1.27/1.48  
% 1.32/1.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
