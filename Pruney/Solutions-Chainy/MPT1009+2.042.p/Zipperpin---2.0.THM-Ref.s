%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KBmpCcyWCd

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:54 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 216 expanded)
%              Number of leaves         :   36 (  79 expanded)
%              Depth                    :   21
%              Number of atoms          :  784 (2692 expanded)
%              Number of equality atoms :   93 ( 220 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X23 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X12
        = ( k1_enumset1 @ X9 @ X10 @ X11 ) )
      | ( X12
        = ( k2_tarski @ X9 @ X11 ) )
      | ( X12
        = ( k2_tarski @ X10 @ X11 ) )
      | ( X12
        = ( k2_tarski @ X9 @ X10 ) )
      | ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12
        = ( k1_tarski @ X10 ) )
      | ( X12
        = ( k1_tarski @ X9 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X25 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X23 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ sk_D @ X0 ) )
      | ( ( k2_relat_1 @ sk_D )
        = ( k9_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('48',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['47','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KBmpCcyWCd
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 539 iterations in 0.263s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.53/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.53/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.71  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.53/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.71  thf(t64_funct_2, conjecture,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.53/0.71         ( m1_subset_1 @
% 0.53/0.71           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.53/0.71       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.53/0.71         ( r1_tarski @
% 0.53/0.71           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.53/0.71           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.53/0.71            ( m1_subset_1 @
% 0.53/0.71              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.53/0.71          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.53/0.71            ( r1_tarski @
% 0.53/0.71              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.53/0.71              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      (~ (r1_tarski @ 
% 0.53/0.71          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.53/0.71          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ 
% 0.53/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(redefinition_k7_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.53/0.71          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.53/0.71      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.53/0.71  thf('3', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.53/0.71           = (k9_relat_1 @ sk_D @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.71  thf('4', plain,
% 0.53/0.71      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.53/0.71          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.53/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.53/0.71  thf(t144_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.53/0.71  thf('5', plain,
% 0.53/0.71      (![X23 : $i, X24 : $i]:
% 0.53/0.71         ((r1_tarski @ (k9_relat_1 @ X23 @ X24) @ (k2_relat_1 @ X23))
% 0.53/0.71          | ~ (v1_relat_1 @ X23))),
% 0.53/0.71      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.53/0.71  thf('6', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ 
% 0.53/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(cc2_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.53/0.71  thf('7', plain,
% 0.53/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.53/0.71         ((v4_relat_1 @ X31 @ X32)
% 0.53/0.71          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.71  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.53/0.71  thf(d18_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      (![X21 : $i, X22 : $i]:
% 0.53/0.71         (~ (v4_relat_1 @ X21 @ X22)
% 0.53/0.71          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.53/0.71          | ~ (v1_relat_1 @ X21))),
% 0.53/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.53/0.71  thf('10', plain,
% 0.53/0.71      ((~ (v1_relat_1 @ sk_D)
% 0.53/0.71        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.71  thf('11', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ 
% 0.53/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(cc1_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( v1_relat_1 @ C ) ))).
% 0.53/0.71  thf('12', plain,
% 0.53/0.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.71         ((v1_relat_1 @ X28)
% 0.53/0.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.53/0.71  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.53/0.71      inference('demod', [status(thm)], ['10', '13'])).
% 0.53/0.71  thf(t69_enumset1, axiom,
% 0.53/0.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.53/0.71  thf('15', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.53/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.71  thf(t70_enumset1, axiom,
% 0.53/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.53/0.71  thf('16', plain,
% 0.53/0.71      (![X4 : $i, X5 : $i]:
% 0.53/0.71         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.53/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.71  thf(t142_zfmisc_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.53/0.71       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.53/0.71            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.53/0.71            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.53/0.71            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.53/0.71            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.53/0.71            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.53/0.71  thf('17', plain,
% 0.53/0.71      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.71         (((X12) = (k1_enumset1 @ X9 @ X10 @ X11))
% 0.53/0.71          | ((X12) = (k2_tarski @ X9 @ X11))
% 0.53/0.71          | ((X12) = (k2_tarski @ X10 @ X11))
% 0.53/0.71          | ((X12) = (k2_tarski @ X9 @ X10))
% 0.53/0.71          | ((X12) = (k1_tarski @ X11))
% 0.53/0.71          | ((X12) = (k1_tarski @ X10))
% 0.53/0.71          | ((X12) = (k1_tarski @ X9))
% 0.53/0.71          | ((X12) = (k1_xboole_0))
% 0.53/0.71          | ~ (r1_tarski @ X12 @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.53/0.71  thf('18', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.53/0.71          | ((X2) = (k1_xboole_0))
% 0.53/0.71          | ((X2) = (k1_tarski @ X1))
% 0.53/0.71          | ((X2) = (k1_tarski @ X1))
% 0.53/0.71          | ((X2) = (k1_tarski @ X0))
% 0.53/0.71          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.53/0.71          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.53/0.71          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.53/0.71          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.53/0.71  thf('19', plain,
% 0.53/0.71      (![X4 : $i, X5 : $i]:
% 0.53/0.71         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.53/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.71  thf('20', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.53/0.71          | ((X2) = (k1_xboole_0))
% 0.53/0.71          | ((X2) = (k1_tarski @ X1))
% 0.53/0.71          | ((X2) = (k1_tarski @ X1))
% 0.53/0.71          | ((X2) = (k1_tarski @ X0))
% 0.53/0.71          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.53/0.71          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.53/0.71          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.53/0.71          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.53/0.71      inference('demod', [status(thm)], ['18', '19'])).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         (((X2) = (k2_tarski @ X1 @ X0))
% 0.53/0.71          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.53/0.71          | ((X2) = (k1_tarski @ X0))
% 0.53/0.71          | ((X2) = (k1_tarski @ X1))
% 0.53/0.71          | ((X2) = (k1_xboole_0))
% 0.53/0.71          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.53/0.71      inference('simplify', [status(thm)], ['20'])).
% 0.53/0.71  thf('22', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.53/0.71          | ((X1) = (k1_xboole_0))
% 0.53/0.71          | ((X1) = (k1_tarski @ X0))
% 0.53/0.71          | ((X1) = (k1_tarski @ X0))
% 0.53/0.71          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.53/0.71          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['15', '21'])).
% 0.53/0.71  thf('23', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         (((X1) = (k2_tarski @ X0 @ X0))
% 0.53/0.71          | ((X1) = (k1_tarski @ X0))
% 0.53/0.71          | ((X1) = (k1_xboole_0))
% 0.53/0.71          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.53/0.71      inference('simplify', [status(thm)], ['22'])).
% 0.53/0.71  thf('24', plain,
% 0.53/0.71      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.53/0.71        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.53/0.71        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['14', '23'])).
% 0.53/0.71  thf('25', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.53/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.71  thf('26', plain,
% 0.53/0.71      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.53/0.71        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.53/0.71        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.53/0.71      inference('demod', [status(thm)], ['24', '25'])).
% 0.53/0.71  thf('27', plain,
% 0.53/0.71      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.53/0.71        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.53/0.71      inference('simplify', [status(thm)], ['26'])).
% 0.53/0.71  thf(t14_funct_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.71       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.53/0.71         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.53/0.71  thf('28', plain,
% 0.53/0.71      (![X26 : $i, X27 : $i]:
% 0.53/0.71         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 0.53/0.71          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 0.53/0.71          | ~ (v1_funct_1 @ X27)
% 0.53/0.71          | ~ (v1_relat_1 @ X27))),
% 0.53/0.71      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.53/0.71  thf('29', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.53/0.71          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.53/0.71          | ~ (v1_relat_1 @ X0)
% 0.53/0.71          | ~ (v1_funct_1 @ X0)
% 0.53/0.71          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.71  thf('30', plain,
% 0.53/0.71      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.53/0.71        | ~ (v1_funct_1 @ sk_D)
% 0.53/0.71        | ~ (v1_relat_1 @ sk_D)
% 0.53/0.71        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.53/0.71      inference('eq_res', [status(thm)], ['29'])).
% 0.53/0.71  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('33', plain,
% 0.53/0.71      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.53/0.71        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.53/0.71      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.53/0.71  thf('34', plain,
% 0.53/0.71      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.53/0.71          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.53/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.53/0.71  thf('35', plain,
% 0.53/0.71      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.53/0.71        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.53/0.71  thf('36', plain,
% 0.53/0.71      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['5', '35'])).
% 0.53/0.71  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('38', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.53/0.71      inference('demod', [status(thm)], ['36', '37'])).
% 0.53/0.71  thf(t65_relat_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ A ) =>
% 0.53/0.71       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.71         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.71  thf('39', plain,
% 0.53/0.71      (![X25 : $i]:
% 0.53/0.71         (((k1_relat_1 @ X25) != (k1_xboole_0))
% 0.53/0.71          | ((k2_relat_1 @ X25) = (k1_xboole_0))
% 0.53/0.71          | ~ (v1_relat_1 @ X25))),
% 0.53/0.71      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.53/0.71  thf('40', plain,
% 0.53/0.71      ((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.71        | ~ (v1_relat_1 @ sk_D)
% 0.53/0.71        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.71  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('42', plain,
% 0.53/0.71      ((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.71        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.53/0.71      inference('demod', [status(thm)], ['40', '41'])).
% 0.53/0.71  thf('43', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.53/0.71      inference('simplify', [status(thm)], ['42'])).
% 0.53/0.71  thf('44', plain,
% 0.53/0.71      (![X23 : $i, X24 : $i]:
% 0.53/0.71         ((r1_tarski @ (k9_relat_1 @ X23 @ X24) @ (k2_relat_1 @ X23))
% 0.53/0.71          | ~ (v1_relat_1 @ X23))),
% 0.53/0.71      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.53/0.71  thf(d10_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.71  thf('45', plain,
% 0.53/0.71      (![X0 : $i, X2 : $i]:
% 0.53/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.53/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.71  thf('46', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ X0)
% 0.53/0.71          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 0.53/0.71          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.53/0.71  thf('47', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (~ (r1_tarski @ k1_xboole_0 @ (k9_relat_1 @ sk_D @ X0))
% 0.53/0.71          | ((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ X0))
% 0.53/0.71          | ~ (v1_relat_1 @ sk_D))),
% 0.53/0.71      inference('sup-', [status(thm)], ['43', '46'])).
% 0.53/0.71  thf(t4_subset_1, axiom,
% 0.53/0.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.53/0.71  thf('48', plain,
% 0.53/0.71      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.53/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.53/0.71  thf(t3_subset, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.71  thf('49', plain,
% 0.53/0.71      (![X15 : $i, X16 : $i]:
% 0.53/0.71         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.71  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.53/0.71      inference('sup-', [status(thm)], ['48', '49'])).
% 0.53/0.71  thf('51', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.53/0.71      inference('simplify', [status(thm)], ['42'])).
% 0.53/0.71  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('53', plain, (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_D @ X0))),
% 0.53/0.71      inference('demod', [status(thm)], ['47', '50', '51', '52'])).
% 0.53/0.71  thf('54', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.53/0.71      inference('sup-', [status(thm)], ['48', '49'])).
% 0.53/0.71  thf('55', plain, ($false),
% 0.53/0.71      inference('demod', [status(thm)], ['4', '53', '54'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
