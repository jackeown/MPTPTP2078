%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CIRigIox2h

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:04 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 751 expanded)
%              Number of leaves         :   52 ( 250 expanded)
%              Depth                    :   17
%              Number of atoms          : 1157 (8789 expanded)
%              Number of equality atoms :  117 ( 534 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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
    ! [X74: $i,X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X76 ) ) )
      | ( ( k7_relset_1 @ X75 @ X76 @ X74 @ X77 )
        = ( k9_relat_1 @ X74 @ X77 ) ) ) ),
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
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( v5_relat_1 @ X71 @ X73 )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) ) ) ),
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
    ! [X51: $i,X52: $i] :
      ( ~ ( v5_relat_1 @ X51 @ X52 )
      | ( r1_tarski @ ( k2_relat_1 @ X51 ) @ X52 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
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
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_relat_1 @ X47 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X53: $i,X54: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ),
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
    ! [X78: $i,X79: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X78 ) @ X79 )
      | ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X78 ) @ X79 ) ) )
      | ~ ( v1_funct_1 @ X78 )
      | ~ ( v1_relat_1 @ X78 ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
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
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( v4_relat_1 @ X71 @ X72 )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v4_relat_1 @ X49 @ X50 )
      | ( r1_tarski @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('31',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X38
        = ( k1_enumset1 @ X35 @ X36 @ X37 ) )
      | ( X38
        = ( k2_tarski @ X35 @ X37 ) )
      | ( X38
        = ( k2_tarski @ X36 @ X37 ) )
      | ( X38
        = ( k2_tarski @ X35 @ X36 ) )
      | ( X38
        = ( k1_tarski @ X37 ) )
      | ( X38
        = ( k1_tarski @ X36 ) )
      | ( X38
        = ( k1_tarski @ X35 ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( r1_tarski @ X38 @ ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('39',plain,(
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
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
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
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('42',plain,(
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
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X66: $i,X67: $i] :
      ( ( ( k1_relat_1 @ X67 )
       != ( k1_tarski @ X66 ) )
      | ( ( k2_relat_1 @ X67 )
        = ( k1_tarski @ ( k1_funct_1 @ X67 @ X66 ) ) )
      | ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_relat_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k2_relat_1 @ sk_D )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_D )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['52'])).

thf('54',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('57',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( v4_relat_1 @ X71 @ X72 )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X60
        = ( k7_relat_1 @ X60 @ X61 ) )
      | ~ ( v4_relat_1 @ X60 @ X61 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('62',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X57 @ X58 ) )
        = ( k9_relat_1 @ X57 @ X58 ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('67',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X55 @ X56 ) @ ( k9_relat_1 @ X55 @ ( k1_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','70'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_zfmisc_1 @ X33 @ X34 )
        = k1_xboole_0 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('73',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X34 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('74',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','70'])).

thf('76',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X34 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('77',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['24','71','73','74','75','76'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('78',plain,(
    ! [X59: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X59 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('79',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['24','71','73','74','75','76'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('80',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('81',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( r2_hidden @ X62 @ ( k1_relat_1 @ X63 ) )
      | ( X64 = k1_xboole_0 )
      | ( X64
       != ( k1_funct_1 @ X63 @ X62 ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('82',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( v1_relat_1 @ X63 )
      | ~ ( v1_funct_1 @ X63 )
      | ( ( k1_funct_1 @ X63 @ X62 )
        = k1_xboole_0 )
      | ( r2_hidden @ X62 @ ( k1_relat_1 @ X63 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','82'])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('84',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('85',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('87',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( r2_hidden @ X69 @ X70 )
      | ~ ( r1_tarski @ X70 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['4','77','78','79','90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CIRigIox2h
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:07:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.87  % Solved by: fo/fo7.sh
% 0.70/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.87  % done 974 iterations in 0.419s
% 0.70/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.87  % SZS output start Refutation
% 0.70/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.70/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.87  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.70/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.87  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.70/0.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.70/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.87  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.70/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.87  thf(sk_D_type, type, sk_D: $i).
% 0.70/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.70/0.87  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.70/0.87  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.70/0.87  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.70/0.87  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.70/0.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.87  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.70/0.87  thf(t64_funct_2, conjecture,
% 0.70/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.87     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.70/0.87         ( m1_subset_1 @
% 0.70/0.87           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.70/0.87       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.70/0.87         ( r1_tarski @
% 0.70/0.87           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.70/0.87           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.70/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.87    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.87        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.70/0.87            ( m1_subset_1 @
% 0.70/0.87              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.70/0.87          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.70/0.87            ( r1_tarski @
% 0.70/0.87              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.70/0.87              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.70/0.87    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.70/0.87  thf('0', plain,
% 0.70/0.87      (~ (r1_tarski @ 
% 0.70/0.87          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.70/0.87          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf('1', plain,
% 0.70/0.87      ((m1_subset_1 @ sk_D @ 
% 0.70/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf(redefinition_k7_relset_1, axiom,
% 0.70/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.87       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.70/0.87  thf('2', plain,
% 0.70/0.87      (![X74 : $i, X75 : $i, X76 : $i, X77 : $i]:
% 0.70/0.87         (~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X76)))
% 0.70/0.87          | ((k7_relset_1 @ X75 @ X76 @ X74 @ X77) = (k9_relat_1 @ X74 @ X77)))),
% 0.70/0.87      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.70/0.87  thf('3', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.70/0.87           = (k9_relat_1 @ sk_D @ X0))),
% 0.70/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.87  thf('4', plain,
% 0.70/0.87      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.70/0.87          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.70/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.70/0.87  thf('5', plain,
% 0.70/0.87      ((m1_subset_1 @ sk_D @ 
% 0.70/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf(cc2_relset_1, axiom,
% 0.70/0.87    (![A:$i,B:$i,C:$i]:
% 0.70/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.70/0.87  thf('6', plain,
% 0.70/0.87      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.70/0.87         ((v5_relat_1 @ X71 @ X73)
% 0.70/0.87          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73))))),
% 0.70/0.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.70/0.87  thf('7', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.70/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.70/0.87  thf(d19_relat_1, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( v1_relat_1 @ B ) =>
% 0.70/0.87       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.70/0.87  thf('8', plain,
% 0.70/0.87      (![X51 : $i, X52 : $i]:
% 0.70/0.87         (~ (v5_relat_1 @ X51 @ X52)
% 0.70/0.87          | (r1_tarski @ (k2_relat_1 @ X51) @ X52)
% 0.70/0.87          | ~ (v1_relat_1 @ X51))),
% 0.70/0.87      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.70/0.87  thf('9', plain,
% 0.70/0.87      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.70/0.87      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.87  thf('10', plain,
% 0.70/0.87      ((m1_subset_1 @ sk_D @ 
% 0.70/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf(cc2_relat_1, axiom,
% 0.70/0.87    (![A:$i]:
% 0.70/0.87     ( ( v1_relat_1 @ A ) =>
% 0.70/0.87       ( ![B:$i]:
% 0.70/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.70/0.87  thf('11', plain,
% 0.70/0.87      (![X47 : $i, X48 : $i]:
% 0.70/0.87         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 0.70/0.87          | (v1_relat_1 @ X47)
% 0.70/0.87          | ~ (v1_relat_1 @ X48))),
% 0.70/0.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.70/0.87  thf('12', plain,
% 0.70/0.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.70/0.87        | (v1_relat_1 @ sk_D))),
% 0.70/0.87      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.87  thf(fc6_relat_1, axiom,
% 0.70/0.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.70/0.87  thf('13', plain,
% 0.70/0.87      (![X53 : $i, X54 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X53 @ X54))),
% 0.70/0.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.70/0.87  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.87  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.70/0.87      inference('demod', [status(thm)], ['9', '14'])).
% 0.70/0.87  thf(t4_funct_2, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.70/0.87       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.70/0.87         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.70/0.87           ( m1_subset_1 @
% 0.70/0.87             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.70/0.87  thf('16', plain,
% 0.70/0.87      (![X78 : $i, X79 : $i]:
% 0.70/0.87         (~ (r1_tarski @ (k2_relat_1 @ X78) @ X79)
% 0.70/0.87          | (m1_subset_1 @ X78 @ 
% 0.70/0.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X78) @ X79)))
% 0.70/0.87          | ~ (v1_funct_1 @ X78)
% 0.70/0.87          | ~ (v1_relat_1 @ X78))),
% 0.70/0.87      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.70/0.87  thf('17', plain,
% 0.70/0.87      ((~ (v1_relat_1 @ sk_D)
% 0.70/0.87        | ~ (v1_funct_1 @ sk_D)
% 0.70/0.87        | (m1_subset_1 @ sk_D @ 
% 0.70/0.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))))),
% 0.70/0.87      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.87  thf('18', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.87  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf('20', plain,
% 0.70/0.87      ((m1_subset_1 @ sk_D @ 
% 0.70/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.70/0.87      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.70/0.87  thf(t3_subset, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.87  thf('21', plain,
% 0.70/0.87      (![X41 : $i, X42 : $i]:
% 0.70/0.87         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.70/0.87      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.87  thf('22', plain,
% 0.70/0.87      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.70/0.87      inference('sup-', [status(thm)], ['20', '21'])).
% 0.70/0.87  thf(d10_xboole_0, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.87  thf('23', plain,
% 0.70/0.87      (![X0 : $i, X2 : $i]:
% 0.70/0.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.70/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.87  thf('24', plain,
% 0.70/0.87      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) @ sk_D)
% 0.70/0.87        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) = (sk_D)))),
% 0.70/0.87      inference('sup-', [status(thm)], ['22', '23'])).
% 0.70/0.87  thf('25', plain,
% 0.70/0.87      ((m1_subset_1 @ sk_D @ 
% 0.70/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf('26', plain,
% 0.70/0.87      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.70/0.87         ((v4_relat_1 @ X71 @ X72)
% 0.70/0.87          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73))))),
% 0.70/0.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.70/0.87  thf('27', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.70/0.87      inference('sup-', [status(thm)], ['25', '26'])).
% 0.70/0.87  thf(d18_relat_1, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( v1_relat_1 @ B ) =>
% 0.70/0.87       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.70/0.87  thf('28', plain,
% 0.70/0.87      (![X49 : $i, X50 : $i]:
% 0.70/0.87         (~ (v4_relat_1 @ X49 @ X50)
% 0.70/0.87          | (r1_tarski @ (k1_relat_1 @ X49) @ X50)
% 0.70/0.87          | ~ (v1_relat_1 @ X49))),
% 0.70/0.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.70/0.87  thf('29', plain,
% 0.70/0.87      ((~ (v1_relat_1 @ sk_D)
% 0.70/0.87        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.70/0.87      inference('sup-', [status(thm)], ['27', '28'])).
% 0.70/0.87  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.87  thf('31', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.70/0.87      inference('demod', [status(thm)], ['29', '30'])).
% 0.70/0.87  thf(t71_enumset1, axiom,
% 0.70/0.87    (![A:$i,B:$i,C:$i]:
% 0.70/0.87     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.70/0.87  thf('32', plain,
% 0.70/0.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.70/0.87         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.70/0.87      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.70/0.87  thf(t70_enumset1, axiom,
% 0.70/0.87    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.70/0.87  thf('33', plain,
% 0.70/0.87      (![X5 : $i, X6 : $i]:
% 0.70/0.87         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.70/0.87      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.70/0.87  thf('34', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i]:
% 0.70/0.87         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.70/0.87      inference('sup+', [status(thm)], ['32', '33'])).
% 0.70/0.87  thf(t69_enumset1, axiom,
% 0.70/0.87    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.70/0.87  thf('35', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.70/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.70/0.87  thf('36', plain,
% 0.70/0.87      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.70/0.87      inference('sup+', [status(thm)], ['34', '35'])).
% 0.70/0.87  thf('37', plain,
% 0.70/0.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.70/0.87         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.70/0.87      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.70/0.87  thf(t142_zfmisc_1, axiom,
% 0.70/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.87     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.70/0.87       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.70/0.87            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.70/0.87            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.70/0.87            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.70/0.87            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.70/0.87            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.70/0.87  thf('38', plain,
% 0.70/0.87      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.70/0.87         (((X38) = (k1_enumset1 @ X35 @ X36 @ X37))
% 0.70/0.87          | ((X38) = (k2_tarski @ X35 @ X37))
% 0.70/0.87          | ((X38) = (k2_tarski @ X36 @ X37))
% 0.70/0.87          | ((X38) = (k2_tarski @ X35 @ X36))
% 0.70/0.87          | ((X38) = (k1_tarski @ X37))
% 0.70/0.87          | ((X38) = (k1_tarski @ X36))
% 0.70/0.87          | ((X38) = (k1_tarski @ X35))
% 0.70/0.87          | ((X38) = (k1_xboole_0))
% 0.70/0.87          | ~ (r1_tarski @ X38 @ (k1_enumset1 @ X35 @ X36 @ X37)))),
% 0.70/0.87      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.70/0.87  thf('39', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.87         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.70/0.87          | ((X3) = (k1_xboole_0))
% 0.70/0.87          | ((X3) = (k1_tarski @ X2))
% 0.70/0.87          | ((X3) = (k1_tarski @ X1))
% 0.70/0.87          | ((X3) = (k1_tarski @ X0))
% 0.70/0.87          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.70/0.87          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.70/0.87          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.70/0.87          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.70/0.87      inference('sup-', [status(thm)], ['37', '38'])).
% 0.70/0.87  thf('40', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i]:
% 0.70/0.87         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.70/0.87          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.70/0.87          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.70/0.87          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.70/0.87          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.70/0.87          | ((X1) = (k1_tarski @ X0))
% 0.70/0.87          | ((X1) = (k1_tarski @ X0))
% 0.70/0.87          | ((X1) = (k1_tarski @ X0))
% 0.70/0.87          | ((X1) = (k1_xboole_0)))),
% 0.70/0.87      inference('sup-', [status(thm)], ['36', '39'])).
% 0.70/0.87  thf('41', plain,
% 0.70/0.87      (![X5 : $i, X6 : $i]:
% 0.70/0.87         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.70/0.87      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.70/0.87  thf('42', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i]:
% 0.70/0.87         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.70/0.87          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.70/0.87          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.70/0.87          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.70/0.87          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.70/0.87          | ((X1) = (k1_tarski @ X0))
% 0.70/0.87          | ((X1) = (k1_tarski @ X0))
% 0.70/0.87          | ((X1) = (k1_tarski @ X0))
% 0.70/0.87          | ((X1) = (k1_xboole_0)))),
% 0.70/0.87      inference('demod', [status(thm)], ['40', '41'])).
% 0.70/0.87  thf('43', plain,
% 0.70/0.87      (![X0 : $i, X1 : $i]:
% 0.70/0.87         (((X1) = (k1_xboole_0))
% 0.70/0.87          | ((X1) = (k1_tarski @ X0))
% 0.70/0.87          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.70/0.87          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.70/0.87      inference('simplify', [status(thm)], ['42'])).
% 0.70/0.87  thf('44', plain,
% 0.70/0.87      ((((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A))
% 0.70/0.87        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.70/0.87        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.70/0.87      inference('sup-', [status(thm)], ['31', '43'])).
% 0.70/0.87  thf('45', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.70/0.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.70/0.87  thf('46', plain,
% 0.70/0.87      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.70/0.87        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.70/0.87        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.70/0.87      inference('demod', [status(thm)], ['44', '45'])).
% 0.70/0.87  thf('47', plain,
% 0.70/0.87      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.70/0.87        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.70/0.87      inference('simplify', [status(thm)], ['46'])).
% 0.70/0.87  thf(t14_funct_1, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.70/0.87       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.70/0.87         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.70/0.87  thf('48', plain,
% 0.70/0.87      (![X66 : $i, X67 : $i]:
% 0.70/0.87         (((k1_relat_1 @ X67) != (k1_tarski @ X66))
% 0.70/0.87          | ((k2_relat_1 @ X67) = (k1_tarski @ (k1_funct_1 @ X67 @ X66)))
% 0.70/0.87          | ~ (v1_funct_1 @ X67)
% 0.70/0.87          | ~ (v1_relat_1 @ X67))),
% 0.70/0.87      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.70/0.87  thf('49', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.70/0.87          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.70/0.87          | ~ (v1_relat_1 @ sk_D)
% 0.70/0.87          | ~ (v1_funct_1 @ sk_D)
% 0.70/0.87          | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.70/0.87      inference('sup-', [status(thm)], ['47', '48'])).
% 0.70/0.87  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.87  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.87  thf('52', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.70/0.87          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.70/0.87          | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.70/0.87      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.70/0.87  thf('53', plain,
% 0.70/0.87      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.70/0.87        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.70/0.87      inference('eq_res', [status(thm)], ['52'])).
% 0.70/0.87  thf('54', plain,
% 0.70/0.87      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.70/0.87          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.70/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.70/0.87  thf('55', plain,
% 0.70/0.87      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.70/0.87        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.70/0.87      inference('sup-', [status(thm)], ['53', '54'])).
% 0.70/0.87  thf('56', plain,
% 0.70/0.87      ((m1_subset_1 @ sk_D @ 
% 0.70/0.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.70/0.87      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.70/0.87  thf('57', plain,
% 0.70/0.87      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.70/0.87         ((v4_relat_1 @ X71 @ X72)
% 0.70/0.87          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73))))),
% 0.70/0.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.70/0.87  thf('58', plain, ((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))),
% 0.70/0.87      inference('sup-', [status(thm)], ['56', '57'])).
% 0.70/0.87  thf(t209_relat_1, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.70/0.87       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.70/0.87  thf('59', plain,
% 0.70/0.87      (![X60 : $i, X61 : $i]:
% 0.70/0.87         (((X60) = (k7_relat_1 @ X60 @ X61))
% 0.70/0.87          | ~ (v4_relat_1 @ X60 @ X61)
% 0.70/0.87          | ~ (v1_relat_1 @ X60))),
% 0.70/0.87      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.70/0.87  thf('60', plain,
% 0.70/0.87      ((~ (v1_relat_1 @ sk_D)
% 0.70/0.87        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 0.70/0.87      inference('sup-', [status(thm)], ['58', '59'])).
% 0.70/0.87  thf('61', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.87  thf('62', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.70/0.87      inference('demod', [status(thm)], ['60', '61'])).
% 0.70/0.87  thf(t148_relat_1, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( v1_relat_1 @ B ) =>
% 0.70/0.87       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.70/0.87  thf('63', plain,
% 0.70/0.87      (![X57 : $i, X58 : $i]:
% 0.70/0.87         (((k2_relat_1 @ (k7_relat_1 @ X57 @ X58)) = (k9_relat_1 @ X57 @ X58))
% 0.70/0.87          | ~ (v1_relat_1 @ X57))),
% 0.70/0.87      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.70/0.87  thf('64', plain,
% 0.70/0.87      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.70/0.87        | ~ (v1_relat_1 @ sk_D))),
% 0.70/0.87      inference('sup+', [status(thm)], ['62', '63'])).
% 0.70/0.87  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.87  thf('66', plain,
% 0.70/0.87      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.70/0.87      inference('demod', [status(thm)], ['64', '65'])).
% 0.70/0.87  thf(t147_relat_1, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( v1_relat_1 @ B ) =>
% 0.70/0.87       ( r1_tarski @
% 0.70/0.87         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.70/0.87  thf('67', plain,
% 0.70/0.87      (![X55 : $i, X56 : $i]:
% 0.70/0.87         ((r1_tarski @ (k9_relat_1 @ X55 @ X56) @ 
% 0.70/0.87           (k9_relat_1 @ X55 @ (k1_relat_1 @ X55)))
% 0.70/0.87          | ~ (v1_relat_1 @ X55))),
% 0.70/0.87      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.70/0.87  thf('68', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.70/0.87          | ~ (v1_relat_1 @ sk_D))),
% 0.70/0.87      inference('sup+', [status(thm)], ['66', '67'])).
% 0.70/0.87  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.87      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.87  thf('70', plain,
% 0.70/0.87      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.70/0.87      inference('demod', [status(thm)], ['68', '69'])).
% 0.70/0.87  thf('71', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.70/0.87      inference('demod', [status(thm)], ['55', '70'])).
% 0.70/0.87  thf(t113_zfmisc_1, axiom,
% 0.70/0.87    (![A:$i,B:$i]:
% 0.70/0.87     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.70/0.87       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.70/0.87  thf('72', plain,
% 0.70/0.87      (![X33 : $i, X34 : $i]:
% 0.70/0.87         (((k2_zfmisc_1 @ X33 @ X34) = (k1_xboole_0))
% 0.70/0.87          | ((X33) != (k1_xboole_0)))),
% 0.70/0.87      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.70/0.87  thf('73', plain,
% 0.70/0.87      (![X34 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X34) = (k1_xboole_0))),
% 0.70/0.87      inference('simplify', [status(thm)], ['72'])).
% 0.70/0.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.70/0.87  thf('74', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.70/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.87  thf('75', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.70/0.87      inference('demod', [status(thm)], ['55', '70'])).
% 0.70/0.87  thf('76', plain,
% 0.70/0.87      (![X34 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X34) = (k1_xboole_0))),
% 0.70/0.87      inference('simplify', [status(thm)], ['72'])).
% 0.70/0.87  thf('77', plain, (((k1_xboole_0) = (sk_D))),
% 0.70/0.87      inference('demod', [status(thm)], ['24', '71', '73', '74', '75', '76'])).
% 0.70/0.87  thf(t150_relat_1, axiom,
% 0.70/0.87    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.87  thf('78', plain,
% 0.70/0.87      (![X59 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X59) = (k1_xboole_0))),
% 0.70/0.87      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.70/0.87  thf('79', plain, (((k1_xboole_0) = (sk_D))),
% 0.70/0.87      inference('demod', [status(thm)], ['24', '71', '73', '74', '75', '76'])).
% 0.70/0.87  thf(t60_relat_1, axiom,
% 0.70/0.87    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.70/0.87     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.70/0.87  thf('80', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.87      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.70/0.87  thf(d4_funct_1, axiom,
% 0.70/0.87    (![A:$i]:
% 0.70/0.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.87       ( ![B:$i,C:$i]:
% 0.70/0.87         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.70/0.87             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.70/0.87               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.70/0.87           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.70/0.87             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.70/0.87               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.70/0.87  thf('81', plain,
% 0.70/0.87      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.70/0.87         ((r2_hidden @ X62 @ (k1_relat_1 @ X63))
% 0.70/0.87          | ((X64) = (k1_xboole_0))
% 0.70/0.87          | ((X64) != (k1_funct_1 @ X63 @ X62))
% 0.70/0.87          | ~ (v1_funct_1 @ X63)
% 0.70/0.87          | ~ (v1_relat_1 @ X63))),
% 0.70/0.87      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.70/0.87  thf('82', plain,
% 0.70/0.87      (![X62 : $i, X63 : $i]:
% 0.70/0.87         (~ (v1_relat_1 @ X63)
% 0.70/0.87          | ~ (v1_funct_1 @ X63)
% 0.70/0.87          | ((k1_funct_1 @ X63 @ X62) = (k1_xboole_0))
% 0.70/0.87          | (r2_hidden @ X62 @ (k1_relat_1 @ X63)))),
% 0.70/0.87      inference('simplify', [status(thm)], ['81'])).
% 0.70/0.87  thf('83', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.70/0.87          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.70/0.87          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.70/0.87          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.70/0.87      inference('sup+', [status(thm)], ['80', '82'])).
% 0.70/0.87  thf(t45_ordinal1, axiom,
% 0.70/0.87    (![A:$i]:
% 0.70/0.87     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.70/0.87       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.70/0.87  thf('84', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.70/0.87      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.70/0.87  thf('85', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.70/0.87      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.70/0.87  thf('86', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.70/0.87          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.70/0.87      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.70/0.87  thf(t7_ordinal1, axiom,
% 0.70/0.87    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.87  thf('87', plain,
% 0.70/0.87      (![X69 : $i, X70 : $i]:
% 0.70/0.87         (~ (r2_hidden @ X69 @ X70) | ~ (r1_tarski @ X70 @ X69))),
% 0.70/0.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.70/0.87  thf('88', plain,
% 0.70/0.87      (![X0 : $i]:
% 0.70/0.87         (((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.70/0.87          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.70/0.87      inference('sup-', [status(thm)], ['86', '87'])).
% 0.70/0.87  thf('89', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.70/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.87  thf('90', plain,
% 0.70/0.87      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.70/0.87      inference('demod', [status(thm)], ['88', '89'])).
% 0.70/0.87  thf('91', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.70/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.87  thf('92', plain, ($false),
% 0.70/0.87      inference('demod', [status(thm)], ['4', '77', '78', '79', '90', '91'])).
% 0.70/0.87  
% 0.70/0.87  % SZS output end Refutation
% 0.70/0.87  
% 0.70/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
