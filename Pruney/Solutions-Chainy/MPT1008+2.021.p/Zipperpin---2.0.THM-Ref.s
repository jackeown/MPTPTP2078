%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LuQ7yXIKGn

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:34 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 401 expanded)
%              Number of leaves         :   46 ( 143 expanded)
%              Depth                    :   20
%              Number of atoms          : 1255 (4563 expanded)
%              Number of equality atoms :  168 ( 537 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X47 ) ) )
      | ( ( k8_relset_1 @ X45 @ X47 @ X46 @ X47 )
        = X45 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X47 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X47 ) ) )
      | ( ( k8_relset_1 @ X45 @ X47 @ X46 @ X47 )
        = X45 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k8_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B_1 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k8_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k10_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
    | ( sk_B_1 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','8','9'])).

thf('11',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    sk_B_1 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
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

thf('30',plain,(
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

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,(
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
      | ( X12 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = o_0_0_xboole_0 )
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
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
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
      | ( X1 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
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
      | ( X1 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = o_0_0_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','37'])).

thf('39',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != ( k1_tarski @ X24 ) )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = o_0_0_xboole_0 ) ),
    inference(eq_res,[status(thm)],['43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('51',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['47','52'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('55',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('56',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('57',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != o_0_0_xboole_0 )
      | ( X23 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('60',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('62',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('63',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('64',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X33 @ X34 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X0 @ o_0_0_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('68',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k8_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k10_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ o_0_0_xboole_0 @ X2 )
      = ( k10_relat_1 @ o_0_0_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ o_0_0_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ o_0_0_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('74',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ o_0_0_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,
    ( o_0_0_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['14','61','78'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('80',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('81',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('82',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('83',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != ( k1_tarski @ X24 ) )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ o_0_0_xboole_0 )
      | ( ( k2_relat_1 @ o_0_0_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('87',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('88',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['86','87'])).

thf(s3_funct_1__e15_31__wellord2,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = ( k1_tarski @ C ) ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('89',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('90',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != o_0_0_xboole_0 )
      | ( X23 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( sk_B @ X43 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ( ( sk_B @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X43: $i] :
      ( v1_funct_1 @ ( sk_B @ X43 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('96',plain,(
    v1_funct_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('98',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('99',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('100',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( o_0_0_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['85','88','96','100'])).

thf('102',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( o_0_0_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','101'])).

thf('103',plain,
    ( o_0_0_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('105',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('106',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('107',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('108',plain,(
    o_0_0_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LuQ7yXIKGn
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.17/1.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.17/1.37  % Solved by: fo/fo7.sh
% 1.17/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.17/1.37  % done 1737 iterations in 0.912s
% 1.17/1.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.17/1.37  % SZS output start Refutation
% 1.17/1.37  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.17/1.37  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.17/1.37  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.17/1.37  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.17/1.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.17/1.37  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.17/1.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.17/1.37  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.17/1.37  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.17/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.17/1.37  thf(sk_C_type, type, sk_C: $i).
% 1.17/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.17/1.37  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.17/1.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.17/1.37  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.17/1.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.17/1.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.17/1.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.17/1.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.17/1.37  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.17/1.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.17/1.37  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 1.17/1.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.17/1.37  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.17/1.37  thf(sk_B_type, type, sk_B: $i > $i).
% 1.17/1.37  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.17/1.37  thf(t62_funct_2, conjecture,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.17/1.37         ( m1_subset_1 @
% 1.17/1.37           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.17/1.37       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.17/1.37         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.17/1.37           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.17/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.17/1.37    (~( ![A:$i,B:$i,C:$i]:
% 1.17/1.37        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.17/1.37            ( m1_subset_1 @
% 1.17/1.37              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.17/1.37          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.17/1.37            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.17/1.37              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 1.17/1.37    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 1.17/1.37  thf('0', plain,
% 1.17/1.37      ((m1_subset_1 @ sk_C @ 
% 1.17/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf(t48_funct_2, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.17/1.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.17/1.37       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.17/1.37         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 1.17/1.37  thf('1', plain,
% 1.17/1.37      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.17/1.37         (((X47) = (k1_xboole_0))
% 1.17/1.37          | ~ (v1_funct_1 @ X46)
% 1.17/1.37          | ~ (v1_funct_2 @ X46 @ X45 @ X47)
% 1.17/1.37          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X47)))
% 1.17/1.37          | ((k8_relset_1 @ X45 @ X47 @ X46 @ X47) = (X45)))),
% 1.17/1.37      inference('cnf', [status(esa)], [t48_funct_2])).
% 1.17/1.37  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 1.17/1.37  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('3', plain,
% 1.17/1.37      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.17/1.37         (((X47) = (o_0_0_xboole_0))
% 1.17/1.37          | ~ (v1_funct_1 @ X46)
% 1.17/1.37          | ~ (v1_funct_2 @ X46 @ X45 @ X47)
% 1.17/1.37          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X47)))
% 1.17/1.37          | ((k8_relset_1 @ X45 @ X47 @ X46 @ X47) = (X45)))),
% 1.17/1.37      inference('demod', [status(thm)], ['1', '2'])).
% 1.17/1.37  thf('4', plain,
% 1.17/1.37      ((((k8_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C @ sk_B_1)
% 1.17/1.37          = (k1_tarski @ sk_A))
% 1.17/1.37        | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.17/1.37        | ~ (v1_funct_1 @ sk_C)
% 1.17/1.37        | ((sk_B_1) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['0', '3'])).
% 1.17/1.37  thf('5', plain,
% 1.17/1.37      ((m1_subset_1 @ sk_C @ 
% 1.17/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf(redefinition_k8_relset_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.17/1.37       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.17/1.37  thf('6', plain,
% 1.17/1.37      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.17/1.37         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.17/1.37          | ((k8_relset_1 @ X40 @ X41 @ X39 @ X42) = (k10_relat_1 @ X39 @ X42)))),
% 1.17/1.37      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.17/1.37  thf('7', plain,
% 1.17/1.37      (![X0 : $i]:
% 1.17/1.37         ((k8_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C @ X0)
% 1.17/1.37           = (k10_relat_1 @ sk_C @ X0))),
% 1.17/1.37      inference('sup-', [status(thm)], ['5', '6'])).
% 1.17/1.37  thf('8', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf('10', plain,
% 1.17/1.37      ((((k10_relat_1 @ sk_C @ sk_B_1) = (k1_tarski @ sk_A))
% 1.17/1.37        | ((sk_B_1) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 1.17/1.37  thf('11', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf('12', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('13', plain, (((sk_B_1) != (o_0_0_xboole_0))),
% 1.17/1.37      inference('demod', [status(thm)], ['11', '12'])).
% 1.17/1.37  thf('14', plain, (((k10_relat_1 @ sk_C @ sk_B_1) = (k1_tarski @ sk_A))),
% 1.17/1.37      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 1.17/1.37  thf('15', plain,
% 1.17/1.37      ((m1_subset_1 @ sk_C @ 
% 1.17/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf(cc2_relset_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.17/1.37       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.17/1.37  thf('16', plain,
% 1.17/1.37      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.17/1.37         ((v4_relat_1 @ X29 @ X30)
% 1.17/1.37          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.17/1.37      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.17/1.37  thf('17', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 1.17/1.37      inference('sup-', [status(thm)], ['15', '16'])).
% 1.17/1.37  thf(d18_relat_1, axiom,
% 1.17/1.37    (![A:$i,B:$i]:
% 1.17/1.37     ( ( v1_relat_1 @ B ) =>
% 1.17/1.37       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.17/1.37  thf('18', plain,
% 1.17/1.37      (![X21 : $i, X22 : $i]:
% 1.17/1.37         (~ (v4_relat_1 @ X21 @ X22)
% 1.17/1.37          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 1.17/1.37          | ~ (v1_relat_1 @ X21))),
% 1.17/1.37      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.17/1.37  thf('19', plain,
% 1.17/1.37      ((~ (v1_relat_1 @ sk_C)
% 1.17/1.37        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['17', '18'])).
% 1.17/1.37  thf('20', plain,
% 1.17/1.37      ((m1_subset_1 @ sk_C @ 
% 1.17/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf(cc1_relset_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.17/1.37       ( v1_relat_1 @ C ) ))).
% 1.17/1.37  thf('21', plain,
% 1.17/1.37      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.17/1.37         ((v1_relat_1 @ X26)
% 1.17/1.37          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.17/1.37      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.17/1.37  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 1.17/1.37      inference('sup-', [status(thm)], ['20', '21'])).
% 1.17/1.37  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 1.17/1.37      inference('demod', [status(thm)], ['19', '22'])).
% 1.17/1.37  thf(t71_enumset1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.17/1.37  thf('24', plain,
% 1.17/1.37      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.17/1.37         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 1.17/1.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.17/1.37  thf(t70_enumset1, axiom,
% 1.17/1.37    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.17/1.37  thf('25', plain,
% 1.17/1.37      (![X4 : $i, X5 : $i]:
% 1.17/1.37         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 1.17/1.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.17/1.37  thf('26', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]:
% 1.17/1.37         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.17/1.37      inference('sup+', [status(thm)], ['24', '25'])).
% 1.17/1.37  thf(t69_enumset1, axiom,
% 1.17/1.37    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.17/1.37  thf('27', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 1.17/1.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.17/1.37  thf('28', plain,
% 1.17/1.37      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.17/1.37      inference('sup+', [status(thm)], ['26', '27'])).
% 1.17/1.37  thf('29', plain,
% 1.17/1.37      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.17/1.37         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 1.17/1.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.17/1.37  thf(t142_zfmisc_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.37     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.17/1.37       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 1.17/1.37            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 1.17/1.37            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 1.17/1.37            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 1.17/1.37            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 1.17/1.37            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 1.17/1.37  thf('30', plain,
% 1.17/1.37      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.17/1.37         (((X12) = (k1_enumset1 @ X9 @ X10 @ X11))
% 1.17/1.37          | ((X12) = (k2_tarski @ X9 @ X11))
% 1.17/1.37          | ((X12) = (k2_tarski @ X10 @ X11))
% 1.17/1.37          | ((X12) = (k2_tarski @ X9 @ X10))
% 1.17/1.37          | ((X12) = (k1_tarski @ X11))
% 1.17/1.37          | ((X12) = (k1_tarski @ X10))
% 1.17/1.37          | ((X12) = (k1_tarski @ X9))
% 1.17/1.37          | ((X12) = (k1_xboole_0))
% 1.17/1.37          | ~ (r1_tarski @ X12 @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 1.17/1.37      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 1.17/1.37  thf('31', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('32', plain,
% 1.17/1.37      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.17/1.37         (((X12) = (k1_enumset1 @ X9 @ X10 @ X11))
% 1.17/1.37          | ((X12) = (k2_tarski @ X9 @ X11))
% 1.17/1.37          | ((X12) = (k2_tarski @ X10 @ X11))
% 1.17/1.37          | ((X12) = (k2_tarski @ X9 @ X10))
% 1.17/1.37          | ((X12) = (k1_tarski @ X11))
% 1.17/1.37          | ((X12) = (k1_tarski @ X10))
% 1.17/1.37          | ((X12) = (k1_tarski @ X9))
% 1.17/1.37          | ((X12) = (o_0_0_xboole_0))
% 1.17/1.37          | ~ (r1_tarski @ X12 @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 1.17/1.37      inference('demod', [status(thm)], ['30', '31'])).
% 1.17/1.37  thf('33', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.37         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 1.17/1.37          | ((X3) = (o_0_0_xboole_0))
% 1.17/1.37          | ((X3) = (k1_tarski @ X2))
% 1.17/1.37          | ((X3) = (k1_tarski @ X1))
% 1.17/1.37          | ((X3) = (k1_tarski @ X0))
% 1.17/1.37          | ((X3) = (k2_tarski @ X2 @ X1))
% 1.17/1.37          | ((X3) = (k2_tarski @ X1 @ X0))
% 1.17/1.37          | ((X3) = (k2_tarski @ X2 @ X0))
% 1.17/1.37          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['29', '32'])).
% 1.17/1.37  thf('34', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]:
% 1.17/1.37         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.17/1.37          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 1.17/1.37          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.17/1.37          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.17/1.37          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.17/1.37          | ((X1) = (k1_tarski @ X0))
% 1.17/1.37          | ((X1) = (k1_tarski @ X0))
% 1.17/1.37          | ((X1) = (k1_tarski @ X0))
% 1.17/1.37          | ((X1) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['28', '33'])).
% 1.17/1.37  thf('35', plain,
% 1.17/1.37      (![X4 : $i, X5 : $i]:
% 1.17/1.37         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 1.17/1.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.17/1.37  thf('36', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]:
% 1.17/1.37         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.17/1.37          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.17/1.37          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.17/1.37          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.17/1.37          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.17/1.37          | ((X1) = (k1_tarski @ X0))
% 1.17/1.37          | ((X1) = (k1_tarski @ X0))
% 1.17/1.37          | ((X1) = (k1_tarski @ X0))
% 1.17/1.37          | ((X1) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('demod', [status(thm)], ['34', '35'])).
% 1.17/1.37  thf('37', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]:
% 1.17/1.37         (((X1) = (o_0_0_xboole_0))
% 1.17/1.37          | ((X1) = (k1_tarski @ X0))
% 1.17/1.37          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.17/1.37          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 1.17/1.37      inference('simplify', [status(thm)], ['36'])).
% 1.17/1.37  thf('38', plain,
% 1.17/1.37      ((((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A))
% 1.17/1.37        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 1.17/1.37        | ((k1_relat_1 @ sk_C) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['23', '37'])).
% 1.17/1.37  thf('39', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 1.17/1.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.17/1.37  thf('40', plain,
% 1.17/1.37      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 1.17/1.37        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 1.17/1.37        | ((k1_relat_1 @ sk_C) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('demod', [status(thm)], ['38', '39'])).
% 1.17/1.37  thf('41', plain,
% 1.17/1.37      ((((k1_relat_1 @ sk_C) = (o_0_0_xboole_0))
% 1.17/1.37        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 1.17/1.37      inference('simplify', [status(thm)], ['40'])).
% 1.17/1.37  thf(t14_funct_1, axiom,
% 1.17/1.37    (![A:$i,B:$i]:
% 1.17/1.37     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.17/1.37       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.17/1.37         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.17/1.37  thf('42', plain,
% 1.17/1.37      (![X24 : $i, X25 : $i]:
% 1.17/1.37         (((k1_relat_1 @ X25) != (k1_tarski @ X24))
% 1.17/1.37          | ((k2_relat_1 @ X25) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 1.17/1.37          | ~ (v1_funct_1 @ X25)
% 1.17/1.37          | ~ (v1_relat_1 @ X25))),
% 1.17/1.37      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.17/1.37  thf('43', plain,
% 1.17/1.37      (![X0 : $i]:
% 1.17/1.37         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 1.17/1.37          | ((k1_relat_1 @ sk_C) = (o_0_0_xboole_0))
% 1.17/1.37          | ~ (v1_relat_1 @ X0)
% 1.17/1.37          | ~ (v1_funct_1 @ X0)
% 1.17/1.37          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 1.17/1.37      inference('sup-', [status(thm)], ['41', '42'])).
% 1.17/1.37  thf('44', plain,
% 1.17/1.37      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.17/1.37        | ~ (v1_funct_1 @ sk_C)
% 1.17/1.37        | ~ (v1_relat_1 @ sk_C)
% 1.17/1.37        | ((k1_relat_1 @ sk_C) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('eq_res', [status(thm)], ['43'])).
% 1.17/1.37  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 1.17/1.37      inference('sup-', [status(thm)], ['20', '21'])).
% 1.17/1.37  thf('47', plain,
% 1.17/1.37      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.17/1.37        | ((k1_relat_1 @ sk_C) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.17/1.37  thf('48', plain,
% 1.17/1.37      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 1.17/1.37         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf('49', plain,
% 1.17/1.37      ((m1_subset_1 @ sk_C @ 
% 1.17/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 1.17/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.37  thf(redefinition_k2_relset_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i]:
% 1.17/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.17/1.37       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.17/1.37  thf('50', plain,
% 1.17/1.37      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.17/1.37         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 1.17/1.37          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 1.17/1.37      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.17/1.37  thf('51', plain,
% 1.17/1.37      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 1.17/1.37         = (k2_relat_1 @ sk_C))),
% 1.17/1.37      inference('sup-', [status(thm)], ['49', '50'])).
% 1.17/1.37  thf('52', plain,
% 1.17/1.37      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.17/1.37      inference('demod', [status(thm)], ['48', '51'])).
% 1.17/1.37  thf('53', plain, (((k1_relat_1 @ sk_C) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('simplify_reflect-', [status(thm)], ['47', '52'])).
% 1.17/1.37  thf(t64_relat_1, axiom,
% 1.17/1.37    (![A:$i]:
% 1.17/1.37     ( ( v1_relat_1 @ A ) =>
% 1.17/1.37       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.17/1.37           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.17/1.37         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.17/1.37  thf('54', plain,
% 1.17/1.37      (![X23 : $i]:
% 1.17/1.37         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 1.17/1.37          | ((X23) = (k1_xboole_0))
% 1.17/1.37          | ~ (v1_relat_1 @ X23))),
% 1.17/1.37      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.17/1.37  thf('55', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('56', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('57', plain,
% 1.17/1.37      (![X23 : $i]:
% 1.17/1.37         (((k1_relat_1 @ X23) != (o_0_0_xboole_0))
% 1.17/1.37          | ((X23) = (o_0_0_xboole_0))
% 1.17/1.37          | ~ (v1_relat_1 @ X23))),
% 1.17/1.37      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.17/1.37  thf('58', plain,
% 1.17/1.37      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 1.17/1.37        | ~ (v1_relat_1 @ sk_C)
% 1.17/1.37        | ((sk_C) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['53', '57'])).
% 1.17/1.37  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 1.17/1.37      inference('sup-', [status(thm)], ['20', '21'])).
% 1.17/1.37  thf('60', plain,
% 1.17/1.37      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)) | ((sk_C) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('demod', [status(thm)], ['58', '59'])).
% 1.17/1.37  thf('61', plain, (((sk_C) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('simplify', [status(thm)], ['60'])).
% 1.17/1.37  thf(t4_subset_1, axiom,
% 1.17/1.37    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.17/1.37  thf('62', plain,
% 1.17/1.37      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 1.17/1.37      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.17/1.37  thf('63', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('64', plain,
% 1.17/1.37      (![X14 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 1.17/1.37      inference('demod', [status(thm)], ['62', '63'])).
% 1.17/1.37  thf(dt_k8_relset_1, axiom,
% 1.17/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.17/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.17/1.37       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.17/1.37  thf('65', plain,
% 1.17/1.37      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.17/1.37         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.17/1.37          | (m1_subset_1 @ (k8_relset_1 @ X33 @ X34 @ X32 @ X35) @ 
% 1.17/1.37             (k1_zfmisc_1 @ X33)))),
% 1.17/1.37      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 1.17/1.37  thf('66', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.17/1.37         (m1_subset_1 @ (k8_relset_1 @ X1 @ X0 @ o_0_0_xboole_0 @ X2) @ 
% 1.17/1.37          (k1_zfmisc_1 @ X1))),
% 1.17/1.37      inference('sup-', [status(thm)], ['64', '65'])).
% 1.17/1.37  thf('67', plain,
% 1.17/1.37      (![X14 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 1.17/1.37      inference('demod', [status(thm)], ['62', '63'])).
% 1.17/1.37  thf('68', plain,
% 1.17/1.37      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.17/1.37         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.17/1.37          | ((k8_relset_1 @ X40 @ X41 @ X39 @ X42) = (k10_relat_1 @ X39 @ X42)))),
% 1.17/1.37      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.17/1.37  thf('69', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.17/1.37         ((k8_relset_1 @ X1 @ X0 @ o_0_0_xboole_0 @ X2)
% 1.17/1.37           = (k10_relat_1 @ o_0_0_xboole_0 @ X2))),
% 1.17/1.37      inference('sup-', [status(thm)], ['67', '68'])).
% 1.17/1.37  thf('70', plain,
% 1.17/1.37      (![X1 : $i, X2 : $i]:
% 1.17/1.37         (m1_subset_1 @ (k10_relat_1 @ o_0_0_xboole_0 @ X2) @ 
% 1.17/1.37          (k1_zfmisc_1 @ X1))),
% 1.17/1.37      inference('demod', [status(thm)], ['66', '69'])).
% 1.17/1.37  thf(t3_subset, axiom,
% 1.17/1.37    (![A:$i,B:$i]:
% 1.17/1.37     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.17/1.37  thf('71', plain,
% 1.17/1.37      (![X15 : $i, X16 : $i]:
% 1.17/1.37         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.17/1.37      inference('cnf', [status(esa)], [t3_subset])).
% 1.17/1.37  thf('72', plain,
% 1.17/1.37      (![X0 : $i, X1 : $i]:
% 1.17/1.37         (r1_tarski @ (k10_relat_1 @ o_0_0_xboole_0 @ X1) @ X0)),
% 1.17/1.37      inference('sup-', [status(thm)], ['70', '71'])).
% 1.17/1.37  thf('73', plain,
% 1.17/1.37      (![X14 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 1.17/1.37      inference('demod', [status(thm)], ['62', '63'])).
% 1.17/1.37  thf('74', plain,
% 1.17/1.37      (![X15 : $i, X16 : $i]:
% 1.17/1.37         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.17/1.37      inference('cnf', [status(esa)], [t3_subset])).
% 1.17/1.37  thf('75', plain, (![X0 : $i]: (r1_tarski @ o_0_0_xboole_0 @ X0)),
% 1.17/1.37      inference('sup-', [status(thm)], ['73', '74'])).
% 1.17/1.37  thf(d10_xboole_0, axiom,
% 1.17/1.37    (![A:$i,B:$i]:
% 1.17/1.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.17/1.37  thf('76', plain,
% 1.17/1.37      (![X0 : $i, X2 : $i]:
% 1.17/1.37         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.17/1.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.17/1.37  thf('77', plain,
% 1.17/1.37      (![X0 : $i]:
% 1.17/1.37         (~ (r1_tarski @ X0 @ o_0_0_xboole_0) | ((X0) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['75', '76'])).
% 1.17/1.37  thf('78', plain,
% 1.17/1.37      (![X0 : $i]: ((k10_relat_1 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('sup-', [status(thm)], ['72', '77'])).
% 1.17/1.37  thf('79', plain, (((o_0_0_xboole_0) = (k1_tarski @ sk_A))),
% 1.17/1.37      inference('demod', [status(thm)], ['14', '61', '78'])).
% 1.17/1.37  thf(t60_relat_1, axiom,
% 1.17/1.37    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.17/1.37     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.17/1.37  thf('80', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.17/1.37  thf('81', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('82', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('83', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.17/1.37  thf('84', plain,
% 1.17/1.37      (![X24 : $i, X25 : $i]:
% 1.17/1.37         (((k1_relat_1 @ X25) != (k1_tarski @ X24))
% 1.17/1.37          | ((k2_relat_1 @ X25) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 1.17/1.37          | ~ (v1_funct_1 @ X25)
% 1.17/1.37          | ~ (v1_relat_1 @ X25))),
% 1.17/1.37      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.17/1.37  thf('85', plain,
% 1.17/1.37      (![X0 : $i]:
% 1.17/1.37         (((o_0_0_xboole_0) != (k1_tarski @ X0))
% 1.17/1.37          | ~ (v1_relat_1 @ o_0_0_xboole_0)
% 1.17/1.37          | ~ (v1_funct_1 @ o_0_0_xboole_0)
% 1.17/1.37          | ((k2_relat_1 @ o_0_0_xboole_0)
% 1.17/1.37              = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ X0))))),
% 1.17/1.37      inference('sup-', [status(thm)], ['83', '84'])).
% 1.17/1.37  thf('86', plain,
% 1.17/1.37      (![X14 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 1.17/1.37      inference('demod', [status(thm)], ['62', '63'])).
% 1.17/1.37  thf('87', plain,
% 1.17/1.37      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.17/1.37         ((v1_relat_1 @ X26)
% 1.17/1.37          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.17/1.37      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.17/1.37  thf('88', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 1.17/1.37      inference('sup-', [status(thm)], ['86', '87'])).
% 1.17/1.37  thf(s3_funct_1__e15_31__wellord2, axiom,
% 1.17/1.37    (![A:$i]:
% 1.17/1.37     ( ?[B:$i]:
% 1.17/1.37       ( ( ![C:$i]:
% 1.17/1.37           ( ( r2_hidden @ C @ A ) =>
% 1.17/1.37             ( ( k1_funct_1 @ B @ C ) = ( k1_tarski @ C ) ) ) ) & 
% 1.17/1.37         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 1.17/1.37         ( v1_relat_1 @ B ) ) ))).
% 1.17/1.37  thf('89', plain, (![X43 : $i]: ((k1_relat_1 @ (sk_B @ X43)) = (X43))),
% 1.17/1.37      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 1.17/1.37  thf('90', plain,
% 1.17/1.37      (![X23 : $i]:
% 1.17/1.37         (((k1_relat_1 @ X23) != (o_0_0_xboole_0))
% 1.17/1.37          | ((X23) = (o_0_0_xboole_0))
% 1.17/1.37          | ~ (v1_relat_1 @ X23))),
% 1.17/1.37      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.17/1.37  thf('91', plain,
% 1.17/1.37      (![X0 : $i]:
% 1.17/1.37         (((X0) != (o_0_0_xboole_0))
% 1.17/1.37          | ~ (v1_relat_1 @ (sk_B @ X0))
% 1.17/1.37          | ((sk_B @ X0) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('sup-', [status(thm)], ['89', '90'])).
% 1.17/1.37  thf('92', plain, (![X43 : $i]: (v1_relat_1 @ (sk_B @ X43))),
% 1.17/1.37      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 1.17/1.37  thf('93', plain,
% 1.17/1.37      (![X0 : $i]:
% 1.17/1.37         (((X0) != (o_0_0_xboole_0)) | ((sk_B @ X0) = (o_0_0_xboole_0)))),
% 1.17/1.37      inference('demod', [status(thm)], ['91', '92'])).
% 1.17/1.37  thf('94', plain, (((sk_B @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('simplify', [status(thm)], ['93'])).
% 1.17/1.37  thf('95', plain, (![X43 : $i]: (v1_funct_1 @ (sk_B @ X43))),
% 1.17/1.37      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 1.17/1.37  thf('96', plain, ((v1_funct_1 @ o_0_0_xboole_0)),
% 1.17/1.37      inference('sup+', [status(thm)], ['94', '95'])).
% 1.17/1.37  thf('97', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.17/1.37  thf('98', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('99', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.17/1.37  thf('100', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.17/1.37  thf('101', plain,
% 1.17/1.37      (![X0 : $i]:
% 1.17/1.37         (((o_0_0_xboole_0) != (k1_tarski @ X0))
% 1.17/1.37          | ((o_0_0_xboole_0)
% 1.17/1.37              = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ X0))))),
% 1.17/1.37      inference('demod', [status(thm)], ['85', '88', '96', '100'])).
% 1.17/1.37  thf('102', plain,
% 1.17/1.37      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 1.17/1.37        | ((o_0_0_xboole_0)
% 1.17/1.37            = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ sk_A))))),
% 1.17/1.37      inference('sup-', [status(thm)], ['79', '101'])).
% 1.17/1.37  thf('103', plain,
% 1.17/1.37      (((o_0_0_xboole_0) = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ sk_A)))),
% 1.17/1.37      inference('simplify', [status(thm)], ['102'])).
% 1.17/1.37  thf('104', plain,
% 1.17/1.37      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.17/1.37      inference('demod', [status(thm)], ['48', '51'])).
% 1.17/1.37  thf('105', plain, (((sk_C) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('simplify', [status(thm)], ['60'])).
% 1.17/1.37  thf('106', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.17/1.37  thf('107', plain, (((sk_C) = (o_0_0_xboole_0))),
% 1.17/1.37      inference('simplify', [status(thm)], ['60'])).
% 1.17/1.37  thf('108', plain,
% 1.17/1.37      (((o_0_0_xboole_0) != (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ sk_A)))),
% 1.17/1.37      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 1.17/1.37  thf('109', plain, ($false),
% 1.17/1.37      inference('simplify_reflect-', [status(thm)], ['103', '108'])).
% 1.17/1.37  
% 1.17/1.37  % SZS output end Refutation
% 1.17/1.37  
% 1.17/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
