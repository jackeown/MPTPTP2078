%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JMcksvup30

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:03 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  141 (1038 expanded)
%              Number of leaves         :   36 ( 326 expanded)
%              Depth                    :   19
%              Number of atoms          :  876 (8868 expanded)
%              Number of equality atoms :   65 ( 681 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k7_relset_1 @ X38 @ X39 @ X37 @ X40 )
        = ( k9_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v5_relat_1 @ sk_D_1 @ sk_B ),
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
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['9','14'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X49 ) @ X50 )
      | ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ X50 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) @ sk_D_1 )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X26 @ X27 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
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
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ X31 )
       != ( k1_tarski @ X30 ) )
      | ( ( k2_relat_1 @ X31 )
        = ( k1_tarski @ ( k1_funct_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k2_relat_1 @ sk_D_1 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_D_1 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['39'])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['58','61'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('64',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k1_tarski @ X11 ) )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('69',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['62','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('77',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('78',plain,(
    k1_xboole_0 = sk_D_1 ),
    inference(demod,[status(thm)],['24','45','47','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('80',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['70','73'])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v5_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('91',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['70','73'])).

thf('92',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['70','73'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X26 @ X27 ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    k1_xboole_0 = sk_D_1 ),
    inference(demod,[status(thm)],['24','45','47','75','76','77'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['62','74'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['4','78','100','101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JMcksvup30
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.14/1.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.14/1.33  % Solved by: fo/fo7.sh
% 1.14/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.33  % done 763 iterations in 0.878s
% 1.14/1.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.14/1.33  % SZS output start Refutation
% 1.14/1.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.14/1.33  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.14/1.33  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.14/1.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.14/1.33  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.14/1.33  thf(sk_C_type, type, sk_C: $i).
% 1.14/1.33  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.14/1.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.14/1.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.14/1.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.14/1.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.14/1.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.14/1.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.14/1.33  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.14/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.14/1.33  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.14/1.33  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.14/1.33  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.33  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.14/1.33  thf(t64_funct_2, conjecture,
% 1.14/1.33    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.33     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.14/1.33         ( m1_subset_1 @
% 1.14/1.33           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.14/1.33       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.14/1.33         ( r1_tarski @
% 1.14/1.33           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.14/1.33           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 1.14/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.33    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.33        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.14/1.33            ( m1_subset_1 @
% 1.14/1.33              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.14/1.33          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.14/1.33            ( r1_tarski @
% 1.14/1.33              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.14/1.33              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 1.14/1.33    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 1.14/1.33  thf('0', plain,
% 1.14/1.33      (~ (r1_tarski @ 
% 1.14/1.33          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 1.14/1.33          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('1', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_D_1 @ 
% 1.14/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(redefinition_k7_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.14/1.33  thf('2', plain,
% 1.14/1.33      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.14/1.33          | ((k7_relset_1 @ X38 @ X39 @ X37 @ X40) = (k9_relat_1 @ X37 @ X40)))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.14/1.33  thf('3', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 1.14/1.33           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['1', '2'])).
% 1.14/1.33  thf('4', plain,
% 1.14/1.33      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 1.14/1.33          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.14/1.33      inference('demod', [status(thm)], ['0', '3'])).
% 1.14/1.33  thf('5', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_D_1 @ 
% 1.14/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(cc2_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.14/1.33  thf('6', plain,
% 1.14/1.33      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.14/1.33         ((v5_relat_1 @ X34 @ X36)
% 1.14/1.33          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.14/1.33  thf('7', plain, ((v5_relat_1 @ sk_D_1 @ sk_B)),
% 1.14/1.33      inference('sup-', [status(thm)], ['5', '6'])).
% 1.14/1.33  thf(d19_relat_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( v1_relat_1 @ B ) =>
% 1.14/1.33       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.14/1.33  thf('8', plain,
% 1.14/1.33      (![X22 : $i, X23 : $i]:
% 1.14/1.33         (~ (v5_relat_1 @ X22 @ X23)
% 1.14/1.33          | (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 1.14/1.33          | ~ (v1_relat_1 @ X22))),
% 1.14/1.33      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.14/1.33  thf('9', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B))),
% 1.14/1.33      inference('sup-', [status(thm)], ['7', '8'])).
% 1.14/1.33  thf('10', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_D_1 @ 
% 1.14/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(cc2_relat_1, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( v1_relat_1 @ A ) =>
% 1.14/1.33       ( ![B:$i]:
% 1.14/1.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.14/1.33  thf('11', plain,
% 1.14/1.33      (![X18 : $i, X19 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.14/1.33          | (v1_relat_1 @ X18)
% 1.14/1.33          | ~ (v1_relat_1 @ X19))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.14/1.33  thf('12', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 1.14/1.33        | (v1_relat_1 @ sk_D_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['10', '11'])).
% 1.14/1.33  thf(fc6_relat_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.14/1.33  thf('13', plain,
% 1.14/1.33      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 1.14/1.33      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.14/1.33  thf('14', plain, ((v1_relat_1 @ sk_D_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13'])).
% 1.14/1.33  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B)),
% 1.14/1.33      inference('demod', [status(thm)], ['9', '14'])).
% 1.14/1.33  thf(t4_funct_2, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.33       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.14/1.33         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.14/1.33           ( m1_subset_1 @
% 1.14/1.33             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.14/1.33  thf('16', plain,
% 1.14/1.33      (![X49 : $i, X50 : $i]:
% 1.14/1.33         (~ (r1_tarski @ (k2_relat_1 @ X49) @ X50)
% 1.14/1.33          | (m1_subset_1 @ X49 @ 
% 1.14/1.33             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ X50)))
% 1.14/1.33          | ~ (v1_funct_1 @ X49)
% 1.14/1.33          | ~ (v1_relat_1 @ X49))),
% 1.14/1.33      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.14/1.33  thf('17', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ sk_D_1)
% 1.14/1.33        | ~ (v1_funct_1 @ sk_D_1)
% 1.14/1.33        | (m1_subset_1 @ sk_D_1 @ 
% 1.14/1.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B))))),
% 1.14/1.33      inference('sup-', [status(thm)], ['15', '16'])).
% 1.14/1.33  thf('18', plain, ((v1_relat_1 @ sk_D_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13'])).
% 1.14/1.33  thf('19', plain, ((v1_funct_1 @ sk_D_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('20', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_D_1 @ 
% 1.14/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 1.14/1.33      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.14/1.33  thf(t3_subset, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.14/1.33  thf('21', plain,
% 1.14/1.33      (![X15 : $i, X16 : $i]:
% 1.14/1.33         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.14/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.14/1.33  thf('22', plain,
% 1.14/1.33      ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B))),
% 1.14/1.33      inference('sup-', [status(thm)], ['20', '21'])).
% 1.14/1.33  thf(d10_xboole_0, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.14/1.33  thf('23', plain,
% 1.14/1.33      (![X0 : $i, X2 : $i]:
% 1.14/1.33         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.14/1.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.33  thf('24', plain,
% 1.14/1.33      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B) @ sk_D_1)
% 1.14/1.33        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B) = (sk_D_1)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['22', '23'])).
% 1.14/1.33  thf(t144_relat_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( v1_relat_1 @ B ) =>
% 1.14/1.33       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 1.14/1.33  thf('25', plain,
% 1.14/1.33      (![X26 : $i, X27 : $i]:
% 1.14/1.33         ((r1_tarski @ (k9_relat_1 @ X26 @ X27) @ (k2_relat_1 @ X26))
% 1.14/1.33          | ~ (v1_relat_1 @ X26))),
% 1.14/1.33      inference('cnf', [status(esa)], [t144_relat_1])).
% 1.14/1.33  thf('26', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_D_1 @ 
% 1.14/1.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('27', plain,
% 1.14/1.33      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.14/1.33         ((v4_relat_1 @ X34 @ X35)
% 1.14/1.33          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.14/1.33  thf('28', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 1.14/1.33      inference('sup-', [status(thm)], ['26', '27'])).
% 1.14/1.33  thf(d18_relat_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( v1_relat_1 @ B ) =>
% 1.14/1.33       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.14/1.33  thf('29', plain,
% 1.14/1.33      (![X20 : $i, X21 : $i]:
% 1.14/1.33         (~ (v4_relat_1 @ X20 @ X21)
% 1.14/1.33          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 1.14/1.33          | ~ (v1_relat_1 @ X20))),
% 1.14/1.33      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.14/1.33  thf('30', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ sk_D_1)
% 1.14/1.33        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['28', '29'])).
% 1.14/1.33  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13'])).
% 1.14/1.33  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['30', '31'])).
% 1.14/1.33  thf(l3_zfmisc_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.14/1.33       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.14/1.33  thf('33', plain,
% 1.14/1.33      (![X9 : $i, X10 : $i]:
% 1.14/1.33         (((X10) = (k1_tarski @ X9))
% 1.14/1.33          | ((X10) = (k1_xboole_0))
% 1.14/1.33          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 1.14/1.33      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.14/1.33  thf('34', plain,
% 1.14/1.33      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 1.14/1.33        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['32', '33'])).
% 1.14/1.33  thf(t14_funct_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.33       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.14/1.33         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.14/1.33  thf('35', plain,
% 1.14/1.33      (![X30 : $i, X31 : $i]:
% 1.14/1.33         (((k1_relat_1 @ X31) != (k1_tarski @ X30))
% 1.14/1.33          | ((k2_relat_1 @ X31) = (k1_tarski @ (k1_funct_1 @ X31 @ X30)))
% 1.14/1.33          | ~ (v1_funct_1 @ X31)
% 1.14/1.33          | ~ (v1_relat_1 @ X31))),
% 1.14/1.33      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.14/1.33  thf('36', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 1.14/1.33          | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 1.14/1.33          | ~ (v1_relat_1 @ sk_D_1)
% 1.14/1.33          | ~ (v1_funct_1 @ sk_D_1)
% 1.14/1.33          | ((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ X0))))),
% 1.14/1.33      inference('sup-', [status(thm)], ['34', '35'])).
% 1.14/1.33  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13'])).
% 1.14/1.33  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('39', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 1.14/1.33          | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 1.14/1.33          | ((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ X0))))),
% 1.14/1.33      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.14/1.33  thf('40', plain,
% 1.14/1.33      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 1.14/1.33        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 1.14/1.33      inference('eq_res', [status(thm)], ['39'])).
% 1.14/1.33  thf('41', plain,
% 1.14/1.33      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 1.14/1.33          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.14/1.33      inference('demod', [status(thm)], ['0', '3'])).
% 1.14/1.33  thf('42', plain,
% 1.14/1.33      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 1.14/1.33        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['40', '41'])).
% 1.14/1.33  thf('43', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['25', '42'])).
% 1.14/1.33  thf('44', plain, ((v1_relat_1 @ sk_D_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13'])).
% 1.14/1.33  thf('45', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 1.14/1.33      inference('demod', [status(thm)], ['43', '44'])).
% 1.14/1.33  thf(t113_zfmisc_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.14/1.33       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.14/1.33  thf('46', plain,
% 1.14/1.33      (![X13 : $i, X14 : $i]:
% 1.14/1.33         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 1.14/1.33          | ((X13) != (k1_xboole_0)))),
% 1.14/1.33      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.14/1.33  thf('47', plain,
% 1.14/1.33      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 1.14/1.33      inference('simplify', [status(thm)], ['46'])).
% 1.14/1.33  thf('48', plain,
% 1.14/1.33      (![X13 : $i, X14 : $i]:
% 1.14/1.33         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 1.14/1.33          | ((X14) != (k1_xboole_0)))),
% 1.14/1.33      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.14/1.33  thf('49', plain,
% 1.14/1.33      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 1.14/1.33      inference('simplify', [status(thm)], ['48'])).
% 1.14/1.33  thf('50', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.14/1.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.33  thf('51', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.14/1.33      inference('simplify', [status(thm)], ['50'])).
% 1.14/1.33  thf('52', plain,
% 1.14/1.33      (![X15 : $i, X17 : $i]:
% 1.14/1.33         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 1.14/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.14/1.33  thf('53', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['51', '52'])).
% 1.14/1.33  thf('54', plain,
% 1.14/1.33      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.14/1.33         ((v4_relat_1 @ X34 @ X35)
% 1.14/1.33          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.14/1.33  thf('55', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 1.14/1.33      inference('sup-', [status(thm)], ['53', '54'])).
% 1.14/1.33  thf('56', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 1.14/1.33      inference('sup+', [status(thm)], ['49', '55'])).
% 1.14/1.33  thf('57', plain,
% 1.14/1.33      (![X20 : $i, X21 : $i]:
% 1.14/1.33         (~ (v4_relat_1 @ X20 @ X21)
% 1.14/1.33          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 1.14/1.33          | ~ (v1_relat_1 @ X20))),
% 1.14/1.33      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.14/1.33  thf('58', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (~ (v1_relat_1 @ k1_xboole_0)
% 1.14/1.33          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['56', '57'])).
% 1.14/1.33  thf('59', plain,
% 1.14/1.33      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 1.14/1.33      inference('simplify', [status(thm)], ['46'])).
% 1.14/1.33  thf('60', plain,
% 1.14/1.33      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 1.14/1.33      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.14/1.33  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.14/1.33      inference('sup+', [status(thm)], ['59', '60'])).
% 1.14/1.33  thf('62', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.14/1.33      inference('demod', [status(thm)], ['58', '61'])).
% 1.14/1.33  thf('63', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.14/1.33      inference('demod', [status(thm)], ['58', '61'])).
% 1.14/1.33  thf(t69_enumset1, axiom,
% 1.14/1.33    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.14/1.33  thf('64', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 1.14/1.33      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.14/1.33  thf('65', plain,
% 1.14/1.33      (![X9 : $i, X10 : $i]:
% 1.14/1.33         (((X10) = (k1_tarski @ X9))
% 1.14/1.33          | ((X10) = (k1_xboole_0))
% 1.14/1.33          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 1.14/1.33      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.14/1.33  thf('66', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]:
% 1.14/1.33         (~ (r1_tarski @ X1 @ (k2_tarski @ X0 @ X0))
% 1.14/1.33          | ((X1) = (k1_xboole_0))
% 1.14/1.33          | ((X1) = (k1_tarski @ X0)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['64', '65'])).
% 1.14/1.33  thf('67', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ X0))
% 1.14/1.33          | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['63', '66'])).
% 1.14/1.33  thf('68', plain,
% 1.14/1.33      (![X10 : $i, X11 : $i]:
% 1.14/1.33         ((r1_tarski @ X10 @ (k1_tarski @ X11)) | ((X10) != (k1_xboole_0)))),
% 1.14/1.33      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.14/1.33  thf('69', plain,
% 1.14/1.33      (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X11))),
% 1.14/1.33      inference('simplify', [status(thm)], ['68'])).
% 1.14/1.33  thf('70', plain,
% 1.14/1.33      (((r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 1.14/1.33        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.14/1.33      inference('sup+', [status(thm)], ['67', '69'])).
% 1.14/1.33  thf('71', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.14/1.33      inference('demod', [status(thm)], ['58', '61'])).
% 1.14/1.33  thf('72', plain,
% 1.14/1.33      (![X0 : $i, X2 : $i]:
% 1.14/1.33         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.14/1.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.33  thf('73', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 1.14/1.33          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['71', '72'])).
% 1.14/1.33  thf('74', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.14/1.33      inference('clc', [status(thm)], ['70', '73'])).
% 1.14/1.33  thf('75', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.14/1.33      inference('demod', [status(thm)], ['62', '74'])).
% 1.14/1.33  thf('76', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 1.14/1.33      inference('demod', [status(thm)], ['43', '44'])).
% 1.14/1.33  thf('77', plain,
% 1.14/1.33      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 1.14/1.33      inference('simplify', [status(thm)], ['46'])).
% 1.14/1.33  thf('78', plain, (((k1_xboole_0) = (sk_D_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['24', '45', '47', '75', '76', '77'])).
% 1.14/1.33  thf('79', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.14/1.33      inference('demod', [status(thm)], ['58', '61'])).
% 1.14/1.33  thf('80', plain,
% 1.14/1.33      (![X15 : $i, X17 : $i]:
% 1.14/1.33         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 1.14/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.14/1.33  thf('81', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['79', '80'])).
% 1.14/1.33  thf('82', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.14/1.33      inference('clc', [status(thm)], ['70', '73'])).
% 1.14/1.33  thf('83', plain,
% 1.14/1.33      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.14/1.33      inference('demod', [status(thm)], ['81', '82'])).
% 1.14/1.33  thf('84', plain,
% 1.14/1.33      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.14/1.33         ((v5_relat_1 @ X34 @ X36)
% 1.14/1.33          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.14/1.33  thf('85', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 1.14/1.33      inference('sup-', [status(thm)], ['83', '84'])).
% 1.14/1.33  thf('86', plain,
% 1.14/1.33      (![X22 : $i, X23 : $i]:
% 1.14/1.33         (~ (v5_relat_1 @ X22 @ X23)
% 1.14/1.33          | (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 1.14/1.33          | ~ (v1_relat_1 @ X22))),
% 1.14/1.33      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.14/1.33  thf('87', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (~ (v1_relat_1 @ k1_xboole_0)
% 1.14/1.33          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['85', '86'])).
% 1.14/1.33  thf('88', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.14/1.33      inference('sup+', [status(thm)], ['59', '60'])).
% 1.14/1.33  thf('89', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 1.14/1.33      inference('demod', [status(thm)], ['87', '88'])).
% 1.14/1.33  thf('90', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 1.14/1.33          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['71', '72'])).
% 1.14/1.33  thf('91', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.14/1.33      inference('clc', [status(thm)], ['70', '73'])).
% 1.14/1.33  thf('92', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.14/1.33      inference('clc', [status(thm)], ['70', '73'])).
% 1.14/1.33  thf('93', plain,
% 1.14/1.33      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.14/1.33      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.14/1.33  thf('94', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['89', '93'])).
% 1.14/1.33  thf('95', plain,
% 1.14/1.33      (![X26 : $i, X27 : $i]:
% 1.14/1.33         ((r1_tarski @ (k9_relat_1 @ X26 @ X27) @ (k2_relat_1 @ X26))
% 1.14/1.33          | ~ (v1_relat_1 @ X26))),
% 1.14/1.33      inference('cnf', [status(esa)], [t144_relat_1])).
% 1.14/1.33  thf('96', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 1.14/1.33          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.14/1.33      inference('sup+', [status(thm)], ['94', '95'])).
% 1.14/1.33  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.14/1.33      inference('sup+', [status(thm)], ['59', '60'])).
% 1.14/1.33  thf('98', plain,
% 1.14/1.33      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 1.14/1.33      inference('demod', [status(thm)], ['96', '97'])).
% 1.14/1.33  thf('99', plain,
% 1.14/1.33      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.14/1.33      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.14/1.33  thf('100', plain,
% 1.14/1.33      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['98', '99'])).
% 1.14/1.33  thf('101', plain, (((k1_xboole_0) = (sk_D_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['24', '45', '47', '75', '76', '77'])).
% 1.14/1.33  thf('102', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.14/1.33      inference('demod', [status(thm)], ['62', '74'])).
% 1.14/1.33  thf('103', plain, ($false),
% 1.14/1.33      inference('demod', [status(thm)], ['4', '78', '100', '101', '102'])).
% 1.14/1.33  
% 1.14/1.33  % SZS output end Refutation
% 1.14/1.33  
% 1.14/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
