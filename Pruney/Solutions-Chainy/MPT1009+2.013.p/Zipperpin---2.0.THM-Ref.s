%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c245IWXamu

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 151 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  690 (1414 expanded)
%              Number of equality atoms :   50 (  80 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k9_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X24 @ X25 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8
        = ( k1_tarski @ X7 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != ( k1_tarski @ X28 ) )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X26 ) @ X27 )
      | ( ( k9_relat_1 @ X26 @ X27 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k9_relat_1 @ sk_D @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k9_relat_1 @ sk_D @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relset_1 @ X2 @ X0 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k9_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k9_relat_1 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('50',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v4_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['50','51'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('61',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','52','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_D @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','63'])).

thf('65',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['4','64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c245IWXamu
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:44 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 175 iterations in 0.068s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(t64_funct_2, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.51         ( m1_subset_1 @
% 0.19/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.51       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.51         ( r1_tarski @
% 0.19/0.51           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.19/0.51           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.51            ( m1_subset_1 @
% 0.19/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.51          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.51            ( r1_tarski @
% 0.19/0.51              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.19/0.51              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (~ (r1_tarski @ 
% 0.19/0.51          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.19/0.51          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_D @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.19/0.51          | ((k7_relset_1 @ X41 @ X42 @ X40 @ X43) = (k9_relat_1 @ X40 @ X43)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.19/0.51           = (k9_relat_1 @ sk_D @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.19/0.51          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.51  thf(t144_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X24 : $i, X25 : $i]:
% 0.19/0.51         ((r1_tarski @ (k9_relat_1 @ X24 @ X25) @ (k2_relat_1 @ X24))
% 0.19/0.51          | ~ (v1_relat_1 @ X24))),
% 0.19/0.51      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_D @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc2_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.51         ((v4_relat_1 @ X33 @ X34)
% 0.19/0.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.51  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.51  thf(d18_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         (~ (v4_relat_1 @ X20 @ X21)
% 0.19/0.51          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.19/0.51          | ~ (v1_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_D)
% 0.19/0.51        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_D @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc1_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( v1_relat_1 @ C ) ))).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.51         ((v1_relat_1 @ X30)
% 0.19/0.51          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.51  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['10', '13'])).
% 0.19/0.51  thf(l3_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i]:
% 0.19/0.51         (((X8) = (k1_tarski @ X7))
% 0.19/0.51          | ((X8) = (k1_xboole_0))
% 0.19/0.51          | ~ (r1_tarski @ X8 @ (k1_tarski @ X7)))),
% 0.19/0.51      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.19/0.51        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.51  thf(t14_funct_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.51       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.19/0.51         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X28 : $i, X29 : $i]:
% 0.19/0.51         (((k1_relat_1 @ X29) != (k1_tarski @ X28))
% 0.19/0.51          | ((k2_relat_1 @ X29) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.19/0.51          | ~ (v1_funct_1 @ X29)
% 0.19/0.51          | ~ (v1_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.19/0.51          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.19/0.51        | ~ (v1_funct_1 @ sk_D)
% 0.19/0.51        | ~ (v1_relat_1 @ sk_D)
% 0.19/0.51        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.19/0.51      inference('eq_res', [status(thm)], ['18'])).
% 0.19/0.51  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.19/0.51        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (~ (r1_tarski @ 
% 0.19/0.51          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.19/0.51          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      ((~ (r1_tarski @ 
% 0.19/0.51           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.19/0.51           (k2_relat_1 @ sk_D))
% 0.19/0.51        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.19/0.51           = (k9_relat_1 @ sk_D @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.19/0.51        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '26'])).
% 0.19/0.51  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf('29', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.51  thf(t151_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.51         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (![X26 : $i, X27 : $i]:
% 0.19/0.51         (~ (r1_xboole_0 @ (k1_relat_1 @ X26) @ X27)
% 0.19/0.51          | ((k9_relat_1 @ X26 @ X27) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ sk_D)
% 0.19/0.51          | ((k9_relat_1 @ sk_D @ X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.51  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.51          | ((k9_relat_1 @ sk_D @ X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.51  thf(t4_subset_1, axiom,
% 0.19/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.51  thf(dt_k7_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.19/0.51          | (m1_subset_1 @ (k7_relset_1 @ X37 @ X38 @ X36 @ X39) @ 
% 0.19/0.51             (k1_zfmisc_1 @ X38)))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (m1_subset_1 @ (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 0.19/0.51          (k1_zfmisc_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.51  thf(t3_subset, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (![X14 : $i, X15 : $i]:
% 0.19/0.51         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (r1_tarski @ (k7_relset_1 @ X2 @ X0 @ k1_xboole_0 @ X1) @ X0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.51  thf('39', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.51  thf(d10_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X0 : $i, X2 : $i]:
% 0.19/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k7_relset_1 @ X1 @ k1_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['38', '41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.19/0.51          | ((k7_relset_1 @ X41 @ X42 @ X40 @ X43) = (k9_relat_1 @ X40 @ X43)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.19/0.51           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 0.19/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['42', '45'])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (![X26 : $i, X27 : $i]:
% 0.19/0.51         (((k9_relat_1 @ X26 @ X27) != (k1_xboole_0))
% 0.19/0.51          | (r1_xboole_0 @ (k1_relat_1 @ X26) @ X27)
% 0.19/0.51          | ~ (v1_relat_1 @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.19/0.51  thf('48', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.51          | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.51  thf(t113_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i]:
% 0.19/0.51         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.19/0.51          | ((X11) != (k1_xboole_0)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.51  thf('50', plain,
% 0.19/0.51      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.19/0.51  thf(fc6_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.51  thf('51', plain,
% 0.19/0.51      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.51  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.51      inference('sup+', [status(thm)], ['50', '51'])).
% 0.19/0.51  thf('53', plain,
% 0.19/0.51      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.51  thf('54', plain,
% 0.19/0.51      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.51         ((v4_relat_1 @ X33 @ X34)
% 0.19/0.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.51  thf('55', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.51  thf('56', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         (~ (v4_relat_1 @ X20 @ X21)
% 0.19/0.51          | (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.19/0.51          | ~ (v1_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.51          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.51  thf('58', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.51      inference('sup+', [status(thm)], ['50', '51'])).
% 0.19/0.51  thf('59', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.19/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.51  thf('60', plain,
% 0.19/0.51      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.51  thf('61', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.19/0.51  thf('62', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['48', '52', '61'])).
% 0.19/0.51  thf('63', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.19/0.51      inference('simplify', [status(thm)], ['62'])).
% 0.19/0.51  thf('64', plain, (![X0 : $i]: ((k9_relat_1 @ sk_D @ X0) = (k1_xboole_0))),
% 0.19/0.51      inference('demod', [status(thm)], ['33', '63'])).
% 0.19/0.51  thf('65', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.51  thf('66', plain, ($false),
% 0.19/0.51      inference('demod', [status(thm)], ['4', '64', '65'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
