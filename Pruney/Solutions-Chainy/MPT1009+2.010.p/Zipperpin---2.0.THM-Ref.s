%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.24syYi4WeP

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:49 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 374 expanded)
%              Number of leaves         :   37 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          :  701 (4525 expanded)
%              Number of equality atoms :   61 ( 289 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v5_relat_1 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v5_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['9','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X39 ) @ X40 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X41 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X12
        = ( k2_tarski @ X10 @ X11 ) )
      | ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12
        = ( k1_tarski @ X10 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
       != ( k1_tarski @ X27 ) )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_tarski @ ( k1_funct_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('56',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('57',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['24','51','53','54','55','56'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X26: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('59',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['24','51','53','54','55','56'])).

thf('60',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57','58','59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.24syYi4WeP
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:13:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 767 iterations in 0.284s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.78  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.60/0.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.60/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.78  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.60/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.78  thf(t64_funct_2, conjecture,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.60/0.78         ( m1_subset_1 @
% 0.60/0.78           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.60/0.78       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.60/0.78         ( r1_tarski @
% 0.60/0.78           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.60/0.78           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.78    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.60/0.78            ( m1_subset_1 @
% 0.60/0.78              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.60/0.78          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.60/0.78            ( r1_tarski @
% 0.60/0.78              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.60/0.78              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.60/0.78    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.60/0.78  thf('0', plain,
% 0.60/0.78      (~ (r1_tarski @ 
% 0.60/0.78          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.60/0.78          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('1', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(redefinition_k7_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.60/0.78  thf('2', plain,
% 0.60/0.78      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.60/0.78          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.60/0.78  thf('3', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.60/0.78           = (k9_relat_1 @ sk_D @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.78  thf('4', plain,
% 0.60/0.78      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.60/0.78          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.60/0.78      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.78  thf('5', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(cc2_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.60/0.78  thf('6', plain,
% 0.60/0.78      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.78         ((v5_relat_1 @ X32 @ X34)
% 0.60/0.78          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.78  thf('7', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.60/0.78      inference('sup-', [status(thm)], ['5', '6'])).
% 0.60/0.78  thf(d19_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ B ) =>
% 0.60/0.78       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.60/0.78  thf('8', plain,
% 0.60/0.78      (![X22 : $i, X23 : $i]:
% 0.60/0.78         (~ (v5_relat_1 @ X22 @ X23)
% 0.60/0.78          | (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 0.60/0.78          | ~ (v1_relat_1 @ X22))),
% 0.60/0.78      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.60/0.78  thf('9', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.60/0.78      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.78  thf('10', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(cc1_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( v1_relat_1 @ C ) ))).
% 0.60/0.78  thf('11', plain,
% 0.60/0.78      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.60/0.78         ((v1_relat_1 @ X29)
% 0.60/0.78          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.78  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.78  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.60/0.78      inference('demod', [status(thm)], ['9', '12'])).
% 0.60/0.78  thf(d10_xboole_0, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.78  thf('14', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.60/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.78  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.78      inference('simplify', [status(thm)], ['14'])).
% 0.60/0.78  thf(t11_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ C ) =>
% 0.60/0.78       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.60/0.78           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.60/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.60/0.78  thf('16', plain,
% 0.60/0.78      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.60/0.78         (~ (r1_tarski @ (k1_relat_1 @ X39) @ X40)
% 0.60/0.78          | ~ (r1_tarski @ (k2_relat_1 @ X39) @ X41)
% 0.60/0.78          | (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.60/0.78          | ~ (v1_relat_1 @ X39))),
% 0.60/0.78      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.60/0.78  thf('17', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ X0)
% 0.60/0.78          | (m1_subset_1 @ X0 @ 
% 0.60/0.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.60/0.78          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.60/0.78      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.78  thf('18', plain,
% 0.60/0.78      (((m1_subset_1 @ sk_D @ 
% 0.60/0.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))
% 0.60/0.78        | ~ (v1_relat_1 @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['13', '17'])).
% 0.60/0.78  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.78  thf('20', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.60/0.78      inference('demod', [status(thm)], ['18', '19'])).
% 0.60/0.78  thf(t3_subset, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.78  thf('21', plain,
% 0.60/0.78      (![X17 : $i, X18 : $i]:
% 0.60/0.78         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.78  thf('22', plain,
% 0.60/0.78      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.60/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.78  thf('23', plain,
% 0.60/0.78      (![X0 : $i, X2 : $i]:
% 0.60/0.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.60/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.78  thf('24', plain,
% 0.60/0.78      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) @ sk_D)
% 0.60/0.78        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) = (sk_D)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['22', '23'])).
% 0.60/0.78  thf(t144_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ B ) =>
% 0.60/0.78       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.60/0.78  thf('25', plain,
% 0.60/0.78      (![X24 : $i, X25 : $i]:
% 0.60/0.78         ((r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k2_relat_1 @ X24))
% 0.60/0.78          | ~ (v1_relat_1 @ X24))),
% 0.60/0.78      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.60/0.78  thf('26', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('27', plain,
% 0.60/0.78      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.78         ((v4_relat_1 @ X32 @ X33)
% 0.60/0.78          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.78  thf('28', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.60/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.78  thf(d18_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ B ) =>
% 0.60/0.78       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.60/0.78  thf('29', plain,
% 0.60/0.78      (![X20 : $i, X21 : $i]:
% 0.60/0.78         (~ (v4_relat_1 @ X20 @ X21)
% 0.60/0.78          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.60/0.78          | ~ (v1_relat_1 @ X20))),
% 0.60/0.78      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.60/0.78  thf('30', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D)
% 0.60/0.78        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.78  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.78  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.60/0.78      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.78  thf(t69_enumset1, axiom,
% 0.60/0.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.78  thf('33', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.60/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.78  thf(l45_zfmisc_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.60/0.78       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.60/0.78            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.60/0.78  thf('34', plain,
% 0.60/0.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.78         (((X12) = (k2_tarski @ X10 @ X11))
% 0.60/0.78          | ((X12) = (k1_tarski @ X11))
% 0.60/0.78          | ((X12) = (k1_tarski @ X10))
% 0.60/0.78          | ((X12) = (k1_xboole_0))
% 0.60/0.78          | ~ (r1_tarski @ X12 @ (k2_tarski @ X10 @ X11)))),
% 0.60/0.78      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.60/0.78  thf('35', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.60/0.78          | ((X1) = (k1_xboole_0))
% 0.60/0.78          | ((X1) = (k1_tarski @ X0))
% 0.60/0.78          | ((X1) = (k1_tarski @ X0))
% 0.60/0.78          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['33', '34'])).
% 0.60/0.78  thf('36', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (((X1) = (k2_tarski @ X0 @ X0))
% 0.60/0.78          | ((X1) = (k1_tarski @ X0))
% 0.60/0.78          | ((X1) = (k1_xboole_0))
% 0.60/0.78          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.60/0.78      inference('simplify', [status(thm)], ['35'])).
% 0.60/0.78  thf('37', plain,
% 0.60/0.78      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.60/0.78        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.60/0.78        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['32', '36'])).
% 0.60/0.78  thf('38', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.60/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.78  thf('39', plain,
% 0.60/0.78      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.60/0.78        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.60/0.78        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.60/0.78      inference('demod', [status(thm)], ['37', '38'])).
% 0.60/0.78  thf('40', plain,
% 0.60/0.78      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.60/0.78        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.78      inference('simplify', [status(thm)], ['39'])).
% 0.60/0.78  thf(t14_funct_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.78       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.60/0.78         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.60/0.78  thf('41', plain,
% 0.60/0.78      (![X27 : $i, X28 : $i]:
% 0.60/0.78         (((k1_relat_1 @ X28) != (k1_tarski @ X27))
% 0.60/0.78          | ((k2_relat_1 @ X28) = (k1_tarski @ (k1_funct_1 @ X28 @ X27)))
% 0.60/0.78          | ~ (v1_funct_1 @ X28)
% 0.60/0.78          | ~ (v1_relat_1 @ X28))),
% 0.60/0.78      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.60/0.78  thf('42', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.60/0.78          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.60/0.78          | ~ (v1_relat_1 @ X0)
% 0.60/0.78          | ~ (v1_funct_1 @ X0)
% 0.60/0.78          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['40', '41'])).
% 0.60/0.78  thf('43', plain,
% 0.60/0.78      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.60/0.78        | ~ (v1_funct_1 @ sk_D)
% 0.60/0.78        | ~ (v1_relat_1 @ sk_D)
% 0.60/0.78        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.78      inference('eq_res', [status(thm)], ['42'])).
% 0.60/0.78  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.78  thf('46', plain,
% 0.60/0.78      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.60/0.78        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.78      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.60/0.78  thf('47', plain,
% 0.60/0.78      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.60/0.78          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.60/0.78      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.78  thf('48', plain,
% 0.60/0.78      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.60/0.78        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['46', '47'])).
% 0.60/0.78  thf('49', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['25', '48'])).
% 0.60/0.78  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.78  thf('51', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.60/0.78      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.78  thf(t113_zfmisc_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.60/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.78  thf('52', plain,
% 0.60/0.78      (![X15 : $i, X16 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.60/0.78          | ((X15) != (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.60/0.78  thf('53', plain,
% 0.60/0.78      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['52'])).
% 0.60/0.78  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.60/0.78  thf('54', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.60/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.78  thf('55', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.60/0.78      inference('demod', [status(thm)], ['49', '50'])).
% 0.60/0.78  thf('56', plain,
% 0.60/0.78      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['52'])).
% 0.60/0.78  thf('57', plain, (((k1_xboole_0) = (sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['24', '51', '53', '54', '55', '56'])).
% 0.60/0.78  thf(t150_relat_1, axiom,
% 0.60/0.78    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.60/0.78  thf('58', plain,
% 0.60/0.78      (![X26 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X26) = (k1_xboole_0))),
% 0.60/0.78      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.60/0.78  thf('59', plain, (((k1_xboole_0) = (sk_D))),
% 0.60/0.78      inference('demod', [status(thm)], ['24', '51', '53', '54', '55', '56'])).
% 0.60/0.78  thf('60', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.60/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.78  thf('61', plain, ($false),
% 0.60/0.78      inference('demod', [status(thm)], ['4', '57', '58', '59', '60'])).
% 0.60/0.78  
% 0.60/0.78  % SZS output end Refutation
% 0.60/0.78  
% 0.60/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
