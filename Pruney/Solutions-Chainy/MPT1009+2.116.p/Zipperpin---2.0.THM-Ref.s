%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gSQSwYDK7Z

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:05 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 339 expanded)
%              Number of leaves         :   39 ( 119 expanded)
%              Depth                    :   20
%              Number of atoms          :  985 (3677 expanded)
%              Number of equality atoms :   97 ( 251 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( v5_relat_1 @ X25 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ X41 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X29 @ X30 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_relat_1 @ X23 @ X24 )
      | ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('30',plain,(
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

thf('31',plain,(
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

thf('32',plain,(
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
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
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
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
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
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
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
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relat_1 @ X32 )
       != ( k1_tarski @ X31 ) )
      | ( ( k2_relat_1 @ X32 )
        = ( k1_tarski @ ( k1_funct_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k2_relat_1 @ sk_D )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_D )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('55',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('56',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','54','56'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('60',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('67',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v5_relat_1 @ X25 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('72',plain,(
    ! [X27: $i,X28: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('73',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('76',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X29 @ X30 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['71','72'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','64'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['4','65','82','83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gSQSwYDK7Z
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 269 iterations in 0.144s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.62  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.62  thf(t64_funct_2, conjecture,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.62         ( m1_subset_1 @
% 0.38/0.62           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.62         ( r1_tarski @
% 0.38/0.62           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.38/0.62           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.62            ( m1_subset_1 @
% 0.38/0.62              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.62          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.62            ( r1_tarski @
% 0.38/0.62              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.38/0.62              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (~ (r1_tarski @ 
% 0.38/0.62          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.38/0.62          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_D @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(redefinition_k7_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.38/0.62          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.38/0.62           = (k9_relat_1 @ sk_D @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.38/0.62          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_D @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(cc2_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.62         ((v5_relat_1 @ X33 @ X35)
% 0.38/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.62  thf('7', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.38/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.62  thf(d19_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i]:
% 0.38/0.62         (~ (v5_relat_1 @ X25 @ X26)
% 0.38/0.62          | (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.38/0.62          | ~ (v1_relat_1 @ X25))),
% 0.38/0.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_D @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(cc2_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X21 : $i, X22 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.38/0.62          | (v1_relat_1 @ X21)
% 0.38/0.62          | ~ (v1_relat_1 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.38/0.62        | (v1_relat_1 @ sk_D))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf(fc6_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X27 : $i, X28 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X27 @ X28))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.62  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '14'])).
% 0.38/0.62  thf(t4_funct_2, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.38/0.62         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.38/0.62           ( m1_subset_1 @
% 0.38/0.62             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X40 : $i, X41 : $i]:
% 0.38/0.62         (~ (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 0.38/0.62          | (m1_subset_1 @ X40 @ 
% 0.38/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ X41)))
% 0.38/0.62          | ~ (v1_funct_1 @ X40)
% 0.38/0.62          | ~ (v1_relat_1 @ X40))),
% 0.38/0.62      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ sk_D)
% 0.38/0.62        | ~ (v1_funct_1 @ sk_D)
% 0.38/0.62        | (m1_subset_1 @ sk_D @ 
% 0.38/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.62  thf('18', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_D @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.38/0.62  thf(t144_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X29 : $i, X30 : $i]:
% 0.38/0.62         ((r1_tarski @ (k9_relat_1 @ X29 @ X30) @ (k2_relat_1 @ X29))
% 0.38/0.62          | ~ (v1_relat_1 @ X29))),
% 0.38/0.62      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_D @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.62         ((v4_relat_1 @ X33 @ X34)
% 0.38/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.62  thf('24', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf(d18_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X23 : $i, X24 : $i]:
% 0.38/0.62         (~ (v4_relat_1 @ X23 @ X24)
% 0.38/0.62          | (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.38/0.62          | ~ (v1_relat_1 @ X23))),
% 0.38/0.62      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ sk_D)
% 0.38/0.62        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.62  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.62  thf(t69_enumset1, axiom,
% 0.38/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.62  thf('29', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.62  thf(t70_enumset1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X4 : $i, X5 : $i]:
% 0.38/0.62         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.38/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.62  thf(t142_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.62       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.38/0.62            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.38/0.62            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.38/0.62            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.38/0.62            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.38/0.62            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.62         (((X12) = (k1_enumset1 @ X9 @ X10 @ X11))
% 0.38/0.62          | ((X12) = (k2_tarski @ X9 @ X11))
% 0.38/0.62          | ((X12) = (k2_tarski @ X10 @ X11))
% 0.38/0.62          | ((X12) = (k2_tarski @ X9 @ X10))
% 0.38/0.62          | ((X12) = (k1_tarski @ X11))
% 0.38/0.62          | ((X12) = (k1_tarski @ X10))
% 0.38/0.62          | ((X12) = (k1_tarski @ X9))
% 0.38/0.62          | ((X12) = (k1_xboole_0))
% 0.38/0.62          | ~ (r1_tarski @ X12 @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.62          | ((X2) = (k1_xboole_0))
% 0.38/0.62          | ((X2) = (k1_tarski @ X1))
% 0.38/0.62          | ((X2) = (k1_tarski @ X1))
% 0.38/0.62          | ((X2) = (k1_tarski @ X0))
% 0.38/0.62          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.38/0.62          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.38/0.62          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.38/0.62          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (![X4 : $i, X5 : $i]:
% 0.38/0.62         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.38/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.62          | ((X2) = (k1_xboole_0))
% 0.38/0.62          | ((X2) = (k1_tarski @ X1))
% 0.38/0.62          | ((X2) = (k1_tarski @ X1))
% 0.38/0.62          | ((X2) = (k1_tarski @ X0))
% 0.38/0.62          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.38/0.62          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.38/0.62          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.38/0.62          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (((X2) = (k2_tarski @ X1 @ X0))
% 0.38/0.62          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.38/0.62          | ((X2) = (k1_tarski @ X0))
% 0.38/0.62          | ((X2) = (k1_tarski @ X1))
% 0.38/0.62          | ((X2) = (k1_xboole_0))
% 0.38/0.62          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.38/0.62          | ((X1) = (k1_xboole_0))
% 0.38/0.62          | ((X1) = (k1_tarski @ X0))
% 0.38/0.62          | ((X1) = (k1_tarski @ X0))
% 0.38/0.62          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.62          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['29', '35'])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((X1) = (k2_tarski @ X0 @ X0))
% 0.38/0.62          | ((X1) = (k1_tarski @ X0))
% 0.38/0.62          | ((X1) = (k1_xboole_0))
% 0.38/0.62          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['36'])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.38/0.62        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.38/0.62        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['28', '37'])).
% 0.38/0.62  thf('39', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.38/0.62        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.38/0.62        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.62  thf('41', plain,
% 0.38/0.62      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.38/0.62        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.62  thf(t14_funct_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.38/0.62         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X31 : $i, X32 : $i]:
% 0.38/0.62         (((k1_relat_1 @ X32) != (k1_tarski @ X31))
% 0.38/0.62          | ((k2_relat_1 @ X32) = (k1_tarski @ (k1_funct_1 @ X32 @ X31)))
% 0.38/0.62          | ~ (v1_funct_1 @ X32)
% 0.38/0.62          | ~ (v1_relat_1 @ X32))),
% 0.38/0.62      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.38/0.62          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.38/0.62          | ~ (v1_relat_1 @ sk_D)
% 0.38/0.62          | ~ (v1_funct_1 @ sk_D)
% 0.38/0.62          | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.62  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.38/0.62          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.38/0.62          | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.38/0.62      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.38/0.62        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.62      inference('eq_res', [status(thm)], ['46'])).
% 0.38/0.62  thf('48', plain,
% 0.38/0.62      (~ (r1_tarski @ 
% 0.38/0.62          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.38/0.62          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('49', plain,
% 0.38/0.62      ((~ (r1_tarski @ 
% 0.38/0.62           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.38/0.62           (k2_relat_1 @ sk_D))
% 0.38/0.62        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.62  thf('50', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.38/0.62           = (k9_relat_1 @ sk_D @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.38/0.62        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['49', '50'])).
% 0.38/0.62  thf('52', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['21', '51'])).
% 0.38/0.62  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('54', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.62  thf(t113_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      (![X7 : $i, X8 : $i]:
% 0.38/0.62         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.38/0.62  thf('57', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['20', '54', '56'])).
% 0.38/0.62  thf(t3_subset, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      (![X15 : $i, X16 : $i]:
% 0.38/0.62         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.62  thf('59', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.38/0.62  thf(t4_subset_1, axiom,
% 0.38/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.62  thf('60', plain,
% 0.38/0.62      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.38/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.62  thf('61', plain,
% 0.38/0.62      (![X15 : $i, X16 : $i]:
% 0.38/0.62         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.62  thf('62', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf(d10_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      (![X0 : $i, X2 : $i]:
% 0.38/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.62  thf('65', plain, (((sk_D) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['59', '64'])).
% 0.38/0.62  thf('66', plain,
% 0.38/0.62      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.38/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.62  thf('67', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.62         ((v5_relat_1 @ X33 @ X35)
% 0.38/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.62  thf('68', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.62  thf('69', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i]:
% 0.38/0.62         (~ (v5_relat_1 @ X25 @ X26)
% 0.38/0.62          | (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.38/0.62          | ~ (v1_relat_1 @ X25))),
% 0.38/0.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.62  thf('70', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.62          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.62  thf('71', plain,
% 0.38/0.62      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.38/0.62  thf('72', plain,
% 0.38/0.62      (![X27 : $i, X28 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X27 @ X28))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.62  thf('73', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.62      inference('sup+', [status(thm)], ['71', '72'])).
% 0.38/0.62  thf('74', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.38/0.62      inference('demod', [status(thm)], ['70', '73'])).
% 0.38/0.62  thf('75', plain,
% 0.38/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.62  thf('76', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.38/0.62  thf('77', plain,
% 0.38/0.62      (![X29 : $i, X30 : $i]:
% 0.38/0.62         ((r1_tarski @ (k9_relat_1 @ X29 @ X30) @ (k2_relat_1 @ X29))
% 0.38/0.62          | ~ (v1_relat_1 @ X29))),
% 0.38/0.62      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.38/0.62  thf('78', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.38/0.62          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['76', '77'])).
% 0.38/0.62  thf('79', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.62      inference('sup+', [status(thm)], ['71', '72'])).
% 0.38/0.62  thf('80', plain,
% 0.38/0.62      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.38/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.38/0.62  thf('81', plain,
% 0.38/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.62  thf('82', plain,
% 0.38/0.62      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.38/0.62  thf('83', plain, (((sk_D) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['59', '64'])).
% 0.38/0.62  thf('84', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('85', plain, ($false),
% 0.38/0.62      inference('demod', [status(thm)], ['4', '65', '82', '83', '84'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
