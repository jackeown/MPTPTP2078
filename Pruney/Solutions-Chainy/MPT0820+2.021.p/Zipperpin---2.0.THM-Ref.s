%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0MmUE7GRMg

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:50 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 192 expanded)
%              Number of leaves         :   35 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  691 (1299 expanded)
%              Number of equality atoms :   53 ( 101 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X27: $i] :
      ( ( ( k3_relat_1 @ X27 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X27 ) @ ( k2_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_relat_1 @ X23 @ X24 )
      | ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['6','11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['16','23'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k2_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
      = ( k2_xboole_0 @ sk_A @ ( k3_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = ( k2_xboole_0 @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v5_relat_1 @ X25 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k2_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ ( k3_relat_1 @ sk_C ) ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['29','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k2_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k3_relat_1 @ sk_C ) ) )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','57','58','59'])).

thf('61',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k2_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('64',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','74'])).

thf('76',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['60','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0MmUE7GRMg
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.65/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.87  % Solved by: fo/fo7.sh
% 0.65/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.87  % done 993 iterations in 0.422s
% 0.65/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.87  % SZS output start Refutation
% 0.65/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.65/0.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.65/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.87  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.65/0.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.65/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.65/0.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.65/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.65/0.87  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.65/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.65/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.65/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.65/0.87  thf(t19_relset_1, conjecture,
% 0.65/0.87    (![A:$i,B:$i,C:$i]:
% 0.65/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.87       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.65/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.87    (~( ![A:$i,B:$i,C:$i]:
% 0.65/0.87        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.87          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.65/0.87    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.65/0.87  thf('0', plain,
% 0.65/0.87      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.65/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.87  thf(d6_relat_1, axiom,
% 0.65/0.87    (![A:$i]:
% 0.65/0.87     ( ( v1_relat_1 @ A ) =>
% 0.65/0.87       ( ( k3_relat_1 @ A ) =
% 0.65/0.87         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.65/0.87  thf('1', plain,
% 0.65/0.87      (![X27 : $i]:
% 0.65/0.87         (((k3_relat_1 @ X27)
% 0.65/0.87            = (k2_xboole_0 @ (k1_relat_1 @ X27) @ (k2_relat_1 @ X27)))
% 0.65/0.87          | ~ (v1_relat_1 @ X27))),
% 0.65/0.87      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.65/0.87  thf('2', plain,
% 0.65/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.65/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.87  thf(cc2_relset_1, axiom,
% 0.65/0.87    (![A:$i,B:$i,C:$i]:
% 0.65/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.65/0.87  thf('3', plain,
% 0.65/0.87      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.65/0.87         ((v4_relat_1 @ X30 @ X31)
% 0.65/0.87          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.65/0.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.65/0.87  thf('4', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.65/0.87      inference('sup-', [status(thm)], ['2', '3'])).
% 0.65/0.87  thf(d18_relat_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]:
% 0.65/0.87     ( ( v1_relat_1 @ B ) =>
% 0.65/0.87       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.65/0.87  thf('5', plain,
% 0.65/0.87      (![X23 : $i, X24 : $i]:
% 0.65/0.87         (~ (v4_relat_1 @ X23 @ X24)
% 0.65/0.87          | (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.65/0.87          | ~ (v1_relat_1 @ X23))),
% 0.65/0.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.65/0.87  thf('6', plain,
% 0.65/0.87      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.65/0.87      inference('sup-', [status(thm)], ['4', '5'])).
% 0.65/0.87  thf('7', plain,
% 0.65/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.65/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.87  thf(cc2_relat_1, axiom,
% 0.65/0.87    (![A:$i]:
% 0.65/0.87     ( ( v1_relat_1 @ A ) =>
% 0.65/0.87       ( ![B:$i]:
% 0.65/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.65/0.87  thf('8', plain,
% 0.65/0.87      (![X21 : $i, X22 : $i]:
% 0.65/0.87         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.65/0.87          | (v1_relat_1 @ X21)
% 0.65/0.87          | ~ (v1_relat_1 @ X22))),
% 0.65/0.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.65/0.87  thf('9', plain,
% 0.65/0.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.65/0.87      inference('sup-', [status(thm)], ['7', '8'])).
% 0.65/0.87  thf(fc6_relat_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.65/0.87  thf('10', plain,
% 0.65/0.87      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 0.65/0.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.65/0.87  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.65/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.65/0.87  thf('12', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.65/0.87      inference('demod', [status(thm)], ['6', '11'])).
% 0.65/0.87  thf(l32_xboole_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]:
% 0.65/0.87     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.65/0.87  thf('13', plain,
% 0.65/0.87      (![X0 : $i, X2 : $i]:
% 0.65/0.87         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.65/0.87      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.87  thf('14', plain,
% 0.65/0.87      (((k4_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) = (k1_xboole_0))),
% 0.65/0.87      inference('sup-', [status(thm)], ['12', '13'])).
% 0.65/0.87  thf(t98_xboole_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]:
% 0.65/0.87     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.65/0.87  thf('15', plain,
% 0.65/0.87      (![X13 : $i, X14 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ X13 @ X14)
% 0.65/0.87           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.65/0.87      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.65/0.87  thf('16', plain,
% 0.65/0.87      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C))
% 0.65/0.87         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.65/0.87      inference('sup+', [status(thm)], ['14', '15'])).
% 0.65/0.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.65/0.87  thf('17', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.65/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.65/0.87  thf('18', plain,
% 0.65/0.87      (![X0 : $i, X2 : $i]:
% 0.65/0.87         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.65/0.87      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.87  thf('19', plain,
% 0.65/0.87      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.65/0.87      inference('sup-', [status(thm)], ['17', '18'])).
% 0.65/0.87  thf('20', plain,
% 0.65/0.87      (![X13 : $i, X14 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ X13 @ X14)
% 0.65/0.87           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.65/0.87      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.65/0.87  thf('21', plain,
% 0.65/0.87      (![X0 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.87      inference('sup+', [status(thm)], ['19', '20'])).
% 0.65/0.87  thf(t1_boole, axiom,
% 0.65/0.87    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.87  thf('22', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.65/0.87      inference('cnf', [status(esa)], [t1_boole])).
% 0.65/0.87  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.65/0.87      inference('sup+', [status(thm)], ['21', '22'])).
% 0.65/0.87  thf('24', plain, (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 0.65/0.87      inference('demod', [status(thm)], ['16', '23'])).
% 0.65/0.87  thf(t4_xboole_1, axiom,
% 0.65/0.87    (![A:$i,B:$i,C:$i]:
% 0.65/0.87     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.65/0.87       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.65/0.87  thf('25', plain,
% 0.65/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X12)
% 0.65/0.87           = (k2_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.65/0.87      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.65/0.87  thf('26', plain,
% 0.65/0.87      (![X0 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ sk_A @ X0)
% 0.65/0.87           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X0)))),
% 0.65/0.87      inference('sup+', [status(thm)], ['24', '25'])).
% 0.65/0.87  thf('27', plain,
% 0.65/0.87      ((((k2_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C))
% 0.65/0.87          = (k2_xboole_0 @ sk_A @ (k3_relat_1 @ sk_C)))
% 0.65/0.87        | ~ (v1_relat_1 @ sk_C))),
% 0.65/0.87      inference('sup+', [status(thm)], ['1', '26'])).
% 0.65/0.87  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.65/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.65/0.87  thf('29', plain,
% 0.65/0.87      (((k2_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C))
% 0.65/0.87         = (k2_xboole_0 @ sk_A @ (k3_relat_1 @ sk_C)))),
% 0.65/0.87      inference('demod', [status(thm)], ['27', '28'])).
% 0.65/0.87  thf('30', plain,
% 0.65/0.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.65/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.87  thf('31', plain,
% 0.65/0.87      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.65/0.87         ((v5_relat_1 @ X30 @ X32)
% 0.65/0.87          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.65/0.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.65/0.87  thf('32', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.65/0.87      inference('sup-', [status(thm)], ['30', '31'])).
% 0.65/0.87  thf(d19_relat_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]:
% 0.65/0.87     ( ( v1_relat_1 @ B ) =>
% 0.65/0.87       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.65/0.87  thf('33', plain,
% 0.65/0.87      (![X25 : $i, X26 : $i]:
% 0.65/0.87         (~ (v5_relat_1 @ X25 @ X26)
% 0.65/0.87          | (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.65/0.87          | ~ (v1_relat_1 @ X25))),
% 0.65/0.87      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.65/0.87  thf('34', plain,
% 0.65/0.87      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.65/0.87      inference('sup-', [status(thm)], ['32', '33'])).
% 0.65/0.87  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.65/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.65/0.87  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.65/0.87      inference('demod', [status(thm)], ['34', '35'])).
% 0.65/0.87  thf('37', plain,
% 0.65/0.87      (![X0 : $i, X2 : $i]:
% 0.65/0.87         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.65/0.87      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.87  thf('38', plain,
% 0.65/0.87      (((k4_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.65/0.87      inference('sup-', [status(thm)], ['36', '37'])).
% 0.65/0.87  thf(t44_xboole_1, axiom,
% 0.65/0.87    (![A:$i,B:$i,C:$i]:
% 0.65/0.87     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.65/0.87       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.65/0.87  thf('39', plain,
% 0.65/0.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.65/0.87         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.65/0.87          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.65/0.87      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.65/0.87  thf('40', plain,
% 0.65/0.87      (![X0 : $i]:
% 0.65/0.87         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.65/0.87          | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.65/0.87      inference('sup-', [status(thm)], ['38', '39'])).
% 0.65/0.87  thf('41', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.65/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.65/0.87  thf('42', plain,
% 0.65/0.87      (![X0 : $i]:
% 0.65/0.87         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))),
% 0.65/0.87      inference('demod', [status(thm)], ['40', '41'])).
% 0.65/0.87  thf('43', plain,
% 0.65/0.87      (![X0 : $i, X2 : $i]:
% 0.65/0.87         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.65/0.87      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.87  thf('44', plain,
% 0.65/0.87      (![X0 : $i]:
% 0.65/0.87         ((k4_xboole_0 @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))
% 0.65/0.87           = (k1_xboole_0))),
% 0.65/0.87      inference('sup-', [status(thm)], ['42', '43'])).
% 0.65/0.87  thf('45', plain,
% 0.65/0.87      (![X13 : $i, X14 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ X13 @ X14)
% 0.65/0.87           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.65/0.87      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.65/0.87  thf('46', plain,
% 0.65/0.87      (![X0 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ (k2_relat_1 @ sk_C))
% 0.65/0.87           = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ k1_xboole_0))),
% 0.65/0.87      inference('sup+', [status(thm)], ['44', '45'])).
% 0.65/0.87  thf('47', plain,
% 0.65/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X12)
% 0.65/0.87           = (k2_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.65/0.87      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.65/0.87  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.65/0.87      inference('sup+', [status(thm)], ['21', '22'])).
% 0.65/0.87  thf('49', plain,
% 0.65/0.87      (![X0 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)))
% 0.65/0.87           = (k2_xboole_0 @ sk_B @ X0))),
% 0.65/0.87      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.65/0.87  thf('50', plain,
% 0.65/0.87      (((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ (k3_relat_1 @ sk_C)))
% 0.65/0.87         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.65/0.87      inference('sup+', [status(thm)], ['29', '49'])).
% 0.65/0.87  thf('51', plain,
% 0.65/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X12)
% 0.65/0.87           = (k2_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.65/0.87      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.65/0.87  thf(commutativity_k2_tarski, axiom,
% 0.65/0.87    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.65/0.87  thf('52', plain,
% 0.65/0.87      (![X15 : $i, X16 : $i]:
% 0.65/0.87         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.65/0.87      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.65/0.87  thf(l51_zfmisc_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]:
% 0.65/0.87     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.65/0.87  thf('53', plain,
% 0.65/0.87      (![X19 : $i, X20 : $i]:
% 0.65/0.87         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.65/0.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.65/0.87  thf('54', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]:
% 0.65/0.87         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['52', '53'])).
% 0.65/0.87  thf('55', plain,
% 0.65/0.87      (![X19 : $i, X20 : $i]:
% 0.65/0.87         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.65/0.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.65/0.87  thf('56', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['54', '55'])).
% 0.65/0.87  thf('57', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.65/0.87           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.65/0.87      inference('sup+', [status(thm)], ['51', '56'])).
% 0.65/0.87  thf('58', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['54', '55'])).
% 0.65/0.87  thf('59', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['54', '55'])).
% 0.65/0.87  thf('60', plain,
% 0.65/0.87      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ (k3_relat_1 @ sk_C)))
% 0.65/0.87         = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.65/0.87      inference('demod', [status(thm)], ['50', '57', '58', '59'])).
% 0.65/0.87  thf('61', plain,
% 0.65/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.65/0.87         ((k2_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X12)
% 0.65/0.87           = (k2_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.65/0.87      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.65/0.87  thf('62', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['54', '55'])).
% 0.65/0.87  thf('63', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.87      inference('sup+', [status(thm)], ['54', '55'])).
% 0.65/0.87  thf('64', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.65/0.87      inference('cnf', [status(esa)], [t1_boole])).
% 0.65/0.87  thf('65', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.65/0.87      inference('sup+', [status(thm)], ['63', '64'])).
% 0.65/0.87  thf(t40_xboole_1, axiom,
% 0.65/0.87    (![A:$i,B:$i]:
% 0.65/0.87     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.65/0.87  thf('66', plain,
% 0.65/0.87      (![X5 : $i, X6 : $i]:
% 0.65/0.87         ((k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X6)
% 0.65/0.87           = (k4_xboole_0 @ X5 @ X6))),
% 0.65/0.87      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.87  thf('67', plain,
% 0.65/0.87      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.65/0.87      inference('sup+', [status(thm)], ['65', '66'])).
% 0.65/0.87  thf('68', plain,
% 0.65/0.87      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.65/0.87      inference('sup-', [status(thm)], ['17', '18'])).
% 0.65/0.87  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.65/0.87      inference('demod', [status(thm)], ['67', '68'])).
% 0.65/0.87  thf('70', plain,
% 0.65/0.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.65/0.87         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.65/0.87          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.65/0.87      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.65/0.87  thf('71', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]:
% 0.65/0.87         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.65/0.87          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.65/0.87      inference('sup-', [status(thm)], ['69', '70'])).
% 0.65/0.87  thf('72', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.65/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.65/0.87  thf('73', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.65/0.87      inference('demod', [status(thm)], ['71', '72'])).
% 0.65/0.87  thf('74', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.65/0.87      inference('sup+', [status(thm)], ['62', '73'])).
% 0.65/0.87  thf('75', plain,
% 0.65/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.87         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.65/0.87      inference('sup+', [status(thm)], ['61', '74'])).
% 0.65/0.87  thf('76', plain,
% 0.65/0.87      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.65/0.87      inference('sup+', [status(thm)], ['60', '75'])).
% 0.65/0.87  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.65/0.87  
% 0.65/0.87  % SZS output end Refutation
% 0.65/0.87  
% 0.65/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
