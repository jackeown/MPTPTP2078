%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J5Zn0nvmav

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:06 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 511 expanded)
%              Number of leaves         :   41 ( 182 expanded)
%              Depth                    :   26
%              Number of atoms          : 1015 (5953 expanded)
%              Number of equality atoms :  114 ( 562 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ X28 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X29: $i] :
      ( ( ( k9_relat_1 @ X29 @ ( k1_relat_1 @ X29 ) )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_relat_1 @ X23 @ X24 )
      | ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X13 @ X13 @ X14 @ X15 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X13 @ X13 @ X14 @ X15 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
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

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X19
        = ( k1_enumset1 @ X16 @ X17 @ X18 ) )
      | ( X19
        = ( k2_tarski @ X16 @ X18 ) )
      | ( X19
        = ( k2_tarski @ X17 @ X18 ) )
      | ( X19
        = ( k2_tarski @ X16 @ X17 ) )
      | ( X19
        = ( k1_tarski @ X18 ) )
      | ( X19
        = ( k1_tarski @ X17 ) )
      | ( X19
        = ( k1_tarski @ X16 ) )
      | ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
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
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','33'])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','33'])).

thf('36',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('38',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) )
      | ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X32 ) )
      | ( ( k9_relat_1 @ X32 @ ( k2_tarski @ X31 @ X33 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X32 @ X31 ) @ ( k1_funct_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('45',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_A ) )
      = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','53'])).

thf('55',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('58',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('62',plain,(
    ! [X30: $i] :
      ( ( ( k1_relat_1 @ X30 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X30 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k2_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ X28 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ( ( k2_relat_1 @ sk_D_1 )
        = ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('71',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('73',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('74',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['4','74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J5Zn0nvmav
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 653 iterations in 0.280s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.73  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.52/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.52/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.52/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.73  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.52/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.52/0.73  thf(t64_funct_2, conjecture,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.52/0.73         ( m1_subset_1 @
% 0.52/0.73           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.52/0.73       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.52/0.73         ( r1_tarski @
% 0.52/0.73           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.52/0.73           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.52/0.73            ( m1_subset_1 @
% 0.52/0.73              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.52/0.73          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.52/0.73            ( r1_tarski @
% 0.52/0.73              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.52/0.73              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      (~ (r1_tarski @ 
% 0.52/0.73          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.52/0.73          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(redefinition_k7_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.52/0.74          | ((k7_relset_1 @ X38 @ X39 @ X37 @ X40) = (k9_relat_1 @ X37 @ X40)))),
% 0.52/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.52/0.74  thf('3', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.52/0.74           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.74  thf('4', plain,
% 0.52/0.74      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.52/0.74          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.74  thf(t144_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ B ) =>
% 0.52/0.74       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.52/0.74  thf('5', plain,
% 0.52/0.74      (![X27 : $i, X28 : $i]:
% 0.52/0.74         ((r1_tarski @ (k9_relat_1 @ X27 @ X28) @ (k2_relat_1 @ X27))
% 0.52/0.74          | ~ (v1_relat_1 @ X27))),
% 0.52/0.74      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.52/0.74  thf(t146_relat_1, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ A ) =>
% 0.52/0.74       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.52/0.74  thf('6', plain,
% 0.52/0.74      (![X29 : $i]:
% 0.52/0.74         (((k9_relat_1 @ X29 @ (k1_relat_1 @ X29)) = (k2_relat_1 @ X29))
% 0.52/0.74          | ~ (v1_relat_1 @ X29))),
% 0.52/0.74      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.52/0.74  thf('7', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(cc2_relset_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.74  thf('8', plain,
% 0.52/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.52/0.74         ((v4_relat_1 @ X34 @ X35)
% 0.52/0.74          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.52/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.74  thf('9', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.52/0.74      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.74  thf(d18_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ B ) =>
% 0.52/0.74       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.74  thf('10', plain,
% 0.52/0.74      (![X23 : $i, X24 : $i]:
% 0.52/0.74         (~ (v4_relat_1 @ X23 @ X24)
% 0.52/0.74          | (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.52/0.74          | ~ (v1_relat_1 @ X23))),
% 0.52/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.74  thf('11', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_D_1)
% 0.52/0.74        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.74  thf('12', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_D_1 @ 
% 0.52/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(cc2_relat_1, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ A ) =>
% 0.52/0.74       ( ![B:$i]:
% 0.52/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.74  thf('13', plain,
% 0.52/0.74      (![X21 : $i, X22 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.52/0.74          | (v1_relat_1 @ X21)
% 0.52/0.74          | ~ (v1_relat_1 @ X22))),
% 0.52/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.74  thf('14', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.52/0.74        | (v1_relat_1 @ sk_D_1))),
% 0.52/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.74  thf(fc6_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.74  thf('15', plain,
% 0.52/0.74      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 0.52/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.74  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.52/0.74  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.52/0.74      inference('demod', [status(thm)], ['11', '16'])).
% 0.52/0.74  thf(t71_enumset1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.52/0.74  thf('18', plain,
% 0.52/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.74         ((k2_enumset1 @ X13 @ X13 @ X14 @ X15)
% 0.52/0.74           = (k1_enumset1 @ X13 @ X14 @ X15))),
% 0.52/0.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.52/0.74  thf(t70_enumset1, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.52/0.74  thf('19', plain,
% 0.52/0.74      (![X11 : $i, X12 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('20', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.52/0.74      inference('sup+', [status(thm)], ['18', '19'])).
% 0.52/0.74  thf(t69_enumset1, axiom,
% 0.52/0.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.52/0.74  thf('21', plain,
% 0.52/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf('22', plain,
% 0.52/0.74      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.52/0.74      inference('sup+', [status(thm)], ['20', '21'])).
% 0.52/0.74  thf('23', plain,
% 0.52/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.74         ((k2_enumset1 @ X13 @ X13 @ X14 @ X15)
% 0.52/0.74           = (k1_enumset1 @ X13 @ X14 @ X15))),
% 0.52/0.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.52/0.74  thf(t142_zfmisc_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.74     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.52/0.74       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.52/0.74            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.52/0.74            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.52/0.74            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.52/0.74            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.52/0.74            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.52/0.74  thf('24', plain,
% 0.52/0.74      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.74         (((X19) = (k1_enumset1 @ X16 @ X17 @ X18))
% 0.52/0.74          | ((X19) = (k2_tarski @ X16 @ X18))
% 0.52/0.74          | ((X19) = (k2_tarski @ X17 @ X18))
% 0.52/0.74          | ((X19) = (k2_tarski @ X16 @ X17))
% 0.52/0.74          | ((X19) = (k1_tarski @ X18))
% 0.52/0.74          | ((X19) = (k1_tarski @ X17))
% 0.52/0.74          | ((X19) = (k1_tarski @ X16))
% 0.52/0.74          | ((X19) = (k1_xboole_0))
% 0.52/0.74          | ~ (r1_tarski @ X19 @ (k1_enumset1 @ X16 @ X17 @ X18)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.52/0.74  thf('25', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.74         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.52/0.74          | ((X3) = (k1_xboole_0))
% 0.52/0.74          | ((X3) = (k1_tarski @ X2))
% 0.52/0.74          | ((X3) = (k1_tarski @ X1))
% 0.52/0.74          | ((X3) = (k1_tarski @ X0))
% 0.52/0.74          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.52/0.74          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.52/0.74          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.52/0.74          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.74  thf('26', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.52/0.74          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.52/0.74          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.52/0.74          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['22', '25'])).
% 0.52/0.74  thf('27', plain,
% 0.52/0.74      (![X11 : $i, X12 : $i]:
% 0.52/0.74         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 0.52/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.74  thf('28', plain,
% 0.52/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf('29', plain,
% 0.52/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf('30', plain,
% 0.52/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf('31', plain,
% 0.52/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf('32', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ((X1) = (k1_xboole_0)))),
% 0.52/0.74      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.52/0.74  thf('33', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((X1) = (k1_xboole_0))
% 0.52/0.74          | ((X1) = (k1_tarski @ X0))
% 0.52/0.74          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['32'])).
% 0.52/0.74  thf('34', plain,
% 0.52/0.74      ((((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['17', '33'])).
% 0.52/0.74  thf('35', plain,
% 0.52/0.74      ((((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['17', '33'])).
% 0.52/0.74  thf('36', plain,
% 0.52/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf(d2_tarski, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.52/0.74       ( ![D:$i]:
% 0.52/0.74         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.52/0.74  thf('37', plain,
% 0.52/0.74      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.74         (((X5) != (X4))
% 0.52/0.74          | (r2_hidden @ X5 @ X6)
% 0.52/0.74          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d2_tarski])).
% 0.52/0.74  thf('38', plain,
% 0.52/0.74      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.52/0.74      inference('simplify', [status(thm)], ['37'])).
% 0.52/0.74  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.52/0.74      inference('sup+', [status(thm)], ['36', '38'])).
% 0.52/0.74  thf('40', plain,
% 0.52/0.74      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['35', '39'])).
% 0.52/0.74  thf('41', plain,
% 0.52/0.74      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['35', '39'])).
% 0.52/0.74  thf(t118_funct_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.52/0.74       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.52/0.74           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.52/0.74         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.52/0.74           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.52/0.74  thf('42', plain,
% 0.52/0.74      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X31 @ (k1_relat_1 @ X32))
% 0.52/0.74          | ~ (r2_hidden @ X33 @ (k1_relat_1 @ X32))
% 0.52/0.74          | ((k9_relat_1 @ X32 @ (k2_tarski @ X31 @ X33))
% 0.52/0.74              = (k2_tarski @ (k1_funct_1 @ X32 @ X31) @ 
% 0.52/0.74                 (k1_funct_1 @ X32 @ X33)))
% 0.52/0.74          | ~ (v1_funct_1 @ X32)
% 0.52/0.74          | ~ (v1_relat_1 @ X32))),
% 0.52/0.74      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.52/0.74  thf('43', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74          | ~ (v1_relat_1 @ sk_D_1)
% 0.52/0.74          | ~ (v1_funct_1 @ sk_D_1)
% 0.52/0.74          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ X0))
% 0.52/0.74              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.52/0.74                 (k1_funct_1 @ sk_D_1 @ X0)))
% 0.52/0.74          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['41', '42'])).
% 0.52/0.74  thf('44', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.52/0.74  thf('45', plain, ((v1_funct_1 @ sk_D_1)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('46', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ X0))
% 0.52/0.74              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.52/0.74                 (k1_funct_1 @ sk_D_1 @ X0)))
% 0.52/0.74          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.52/0.74      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.52/0.74  thf('47', plain,
% 0.52/0.74      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74        | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ sk_A))
% 0.52/0.74            = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.52/0.74               (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['40', '46'])).
% 0.52/0.74  thf('48', plain,
% 0.52/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf('49', plain,
% 0.52/0.74      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf('50', plain,
% 0.52/0.74      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74        | ((k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))
% 0.52/0.74            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.52/0.74  thf('51', plain,
% 0.52/0.74      ((((k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))
% 0.52/0.74          = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['50'])).
% 0.52/0.74  thf('52', plain,
% 0.52/0.74      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.52/0.74          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.74  thf('53', plain,
% 0.52/0.74      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.52/0.74           (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['51', '52'])).
% 0.52/0.74  thf('54', plain,
% 0.52/0.74      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.52/0.74           (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['34', '53'])).
% 0.52/0.74  thf('55', plain,
% 0.52/0.74      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.52/0.74        | ~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.52/0.74             (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['54'])).
% 0.52/0.74  thf('56', plain,
% 0.52/0.74      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_D_1)
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['6', '55'])).
% 0.52/0.74  thf('57', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.52/0.74  thf('58', plain,
% 0.52/0.74      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 0.52/0.74        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.74  thf('59', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['5', '58'])).
% 0.52/0.74  thf('60', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.52/0.74  thf('61', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.52/0.74      inference('demod', [status(thm)], ['59', '60'])).
% 0.52/0.74  thf(t65_relat_1, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ A ) =>
% 0.52/0.74       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.74         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.74  thf('62', plain,
% 0.52/0.74      (![X30 : $i]:
% 0.52/0.74         (((k1_relat_1 @ X30) != (k1_xboole_0))
% 0.52/0.74          | ((k2_relat_1 @ X30) = (k1_xboole_0))
% 0.52/0.74          | ~ (v1_relat_1 @ X30))),
% 0.52/0.74      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.52/0.74  thf('63', plain,
% 0.52/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_D_1)
% 0.52/0.74        | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['61', '62'])).
% 0.52/0.74  thf('64', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.52/0.74  thf('65', plain,
% 0.52/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.74        | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('demod', [status(thm)], ['63', '64'])).
% 0.52/0.74  thf('66', plain, (((k2_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['65'])).
% 0.52/0.74  thf('67', plain,
% 0.52/0.74      (![X27 : $i, X28 : $i]:
% 0.52/0.74         ((r1_tarski @ (k9_relat_1 @ X27 @ X28) @ (k2_relat_1 @ X27))
% 0.52/0.74          | ~ (v1_relat_1 @ X27))),
% 0.52/0.74      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.52/0.74  thf(d10_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.74  thf('68', plain,
% 0.52/0.74      (![X0 : $i, X2 : $i]:
% 0.52/0.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.52/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.74  thf('69', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (~ (v1_relat_1 @ X0)
% 0.52/0.74          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 0.52/0.74          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['67', '68'])).
% 0.52/0.74  thf('70', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (r1_tarski @ k1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.52/0.74          | ((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ X0))
% 0.52/0.74          | ~ (v1_relat_1 @ sk_D_1))),
% 0.52/0.74      inference('sup-', [status(thm)], ['66', '69'])).
% 0.52/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.74  thf('71', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.52/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.74  thf('72', plain, (((k2_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['65'])).
% 0.52/0.74  thf('73', plain, ((v1_relat_1 @ sk_D_1)),
% 0.52/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.52/0.74  thf('74', plain, (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.52/0.74      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.52/0.74  thf('75', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.52/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.74  thf('76', plain, ($false),
% 0.52/0.74      inference('demod', [status(thm)], ['4', '74', '75'])).
% 0.52/0.74  
% 0.52/0.74  % SZS output end Refutation
% 0.52/0.74  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
