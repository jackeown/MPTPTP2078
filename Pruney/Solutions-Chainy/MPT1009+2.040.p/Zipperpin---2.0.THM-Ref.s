%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zi14I39ngB

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:54 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 223 expanded)
%              Number of leaves         :   39 (  83 expanded)
%              Depth                    :   19
%              Number of atoms          :  819 (2694 expanded)
%              Number of equality atoms :   99 ( 230 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

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

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X13
        = ( k1_enumset1 @ X10 @ X11 @ X12 ) )
      | ( X13
        = ( k2_tarski @ X10 @ X12 ) )
      | ( X13
        = ( k2_tarski @ X11 @ X12 ) )
      | ( X13
        = ( k2_tarski @ X10 @ X11 ) )
      | ( X13
        = ( k1_tarski @ X12 ) )
      | ( X13
        = ( k1_tarski @ X11 ) )
      | ( X13
        = ( k1_tarski @ X10 ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != ( k1_tarski @ X24 ) )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('47',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('59',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['4','46','57','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zi14I39ngB
% 0.15/0.38  % Computer   : n019.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 19:39:07 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 521 iterations in 0.203s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.69  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.69  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.46/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.69  thf(t64_funct_2, conjecture,
% 0.46/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.69         ( m1_subset_1 @
% 0.46/0.69           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.69       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.69         ( r1_tarski @
% 0.46/0.69           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.46/0.69           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.69            ( m1_subset_1 @
% 0.46/0.69              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.69          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.69            ( r1_tarski @
% 0.46/0.69              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.46/0.69              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.46/0.69  thf('0', plain,
% 0.46/0.69      (~ (r1_tarski @ 
% 0.46/0.69          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.46/0.69          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('1', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_D @ 
% 0.46/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(redefinition_k7_relset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.69       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.46/0.70          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.46/0.70           = (k9_relat_1 @ sk_D @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.46/0.70          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.70  thf(t144_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i]:
% 0.46/0.70         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ (k2_relat_1 @ X21))
% 0.46/0.70          | ~ (v1_relat_1 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X29 @ X30)
% 0.46/0.70          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.70  thf(d18_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (![X19 : $i, X20 : $i]:
% 0.46/0.70         (~ (v4_relat_1 @ X19 @ X20)
% 0.46/0.70          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.46/0.70          | ~ (v1_relat_1 @ X19))),
% 0.46/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_D)
% 0.46/0.70        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( v1_relat_1 @ C ) ))).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X26)
% 0.46/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['10', '13'])).
% 0.46/0.70  thf(t71_enumset1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.70         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.46/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.70  thf(t70_enumset1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.70  thf(t69_enumset1, axiom,
% 0.46/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.70  thf('18', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.70         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.46/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.70  thf(t142_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.70       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.46/0.70            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.46/0.70            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.46/0.70            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.46/0.70            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.46/0.70            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.70         (((X13) = (k1_enumset1 @ X10 @ X11 @ X12))
% 0.46/0.70          | ((X13) = (k2_tarski @ X10 @ X12))
% 0.46/0.70          | ((X13) = (k2_tarski @ X11 @ X12))
% 0.46/0.70          | ((X13) = (k2_tarski @ X10 @ X11))
% 0.46/0.70          | ((X13) = (k1_tarski @ X12))
% 0.46/0.70          | ((X13) = (k1_tarski @ X11))
% 0.46/0.70          | ((X13) = (k1_tarski @ X10))
% 0.46/0.70          | ((X13) = (k1_xboole_0))
% 0.46/0.70          | ~ (r1_tarski @ X13 @ (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.46/0.70          | ((X3) = (k1_xboole_0))
% 0.46/0.70          | ((X3) = (k1_tarski @ X2))
% 0.46/0.70          | ((X3) = (k1_tarski @ X1))
% 0.46/0.70          | ((X3) = (k1_tarski @ X0))
% 0.46/0.70          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.46/0.70          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.46/0.70          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.46/0.70          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.46/0.70          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.46/0.70          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.46/0.70          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['19', '22'])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]:
% 0.46/0.70         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.46/0.70          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.46/0.70          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.46/0.70          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((X1) = (k1_xboole_0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.46/0.70          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['25'])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      ((((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '26'])).
% 0.46/0.70  thf('28', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.46/0.70        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['29'])).
% 0.46/0.70  thf(t14_funct_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.70       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.46/0.70         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (![X24 : $i, X25 : $i]:
% 0.46/0.70         (((k1_relat_1 @ X25) != (k1_tarski @ X24))
% 0.46/0.70          | ((k2_relat_1 @ X25) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 0.46/0.70          | ~ (v1_funct_1 @ X25)
% 0.46/0.70          | ~ (v1_relat_1 @ X25))),
% 0.46/0.70      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.46/0.70          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.46/0.70        | ~ (v1_funct_1 @ sk_D)
% 0.46/0.70        | ~ (v1_relat_1 @ sk_D)
% 0.46/0.70        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.46/0.70      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.70  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.46/0.70        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.46/0.70          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.46/0.70        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['5', '38'])).
% 0.46/0.70  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('41', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.70  thf(t64_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.70           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.70         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.46/0.70          | ((X23) = (k1_xboole_0))
% 0.46/0.70          | ~ (v1_relat_1 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_D)
% 0.46/0.70        | ((sk_D) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.70  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.70  thf('46', plain, (((sk_D) = (k1_xboole_0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.70  thf(t60_relat_1, axiom,
% 0.46/0.70    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.46/0.70     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('47', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i]:
% 0.46/0.70         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ (k2_relat_1 @ X21))
% 0.46/0.70          | ~ (v1_relat_1 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.46/0.70          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['47', '48'])).
% 0.46/0.70  thf(t4_subset_1, axiom,
% 0.46/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.70  thf('51', plain,
% 0.46/0.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X26)
% 0.46/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.46/0.70      inference('demod', [status(thm)], ['49', '52'])).
% 0.46/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.70  thf('54', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.70  thf(d10_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X0 : $i, X2 : $i]:
% 0.46/0.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['53', '56'])).
% 0.46/0.70  thf('58', plain, (((sk_D) = (k1_xboole_0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.70  thf('59', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.70  thf('60', plain, ($false),
% 0.46/0.70      inference('demod', [status(thm)], ['4', '46', '57', '58', '59'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.46/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
