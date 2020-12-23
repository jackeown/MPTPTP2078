%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YiiFN0gucH

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:54 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 388 expanded)
%              Number of leaves         :   37 ( 132 expanded)
%              Depth                    :   17
%              Number of atoms          :  751 (4462 expanded)
%              Number of equality atoms :   56 ( 259 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k7_relset_1 @ X39 @ X40 @ X38 @ X41 )
        = ( k9_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X42 ) @ X43 )
      | ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D ) ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X32 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != ( k1_tarski @ X24 ) )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('46',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('47',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('49',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('50',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','44','46','47','48','49'])).

thf('51',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v5_relat_1 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('59',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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

thf('65',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','44','46','47','48','49'])).

thf('73',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['4','50','71','72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YiiFN0gucH
% 0.14/0.32  % Computer   : n011.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 12:06:42 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.32  % Running portfolio for 600 s
% 0.14/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.33  % Python version: Python 3.6.8
% 0.18/0.33  % Running in FO mode
% 0.18/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.55  % Solved by: fo/fo7.sh
% 0.18/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.55  % done 257 iterations in 0.111s
% 0.18/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.55  % SZS output start Refutation
% 0.18/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.18/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.18/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.18/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.18/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.18/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.18/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.18/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.18/0.55  thf(t64_funct_2, conjecture,
% 0.18/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.18/0.55         ( m1_subset_1 @
% 0.18/0.55           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.18/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.18/0.55         ( r1_tarski @
% 0.18/0.55           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.18/0.55           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.18/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.55        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.18/0.55            ( m1_subset_1 @
% 0.18/0.55              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.18/0.55          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.18/0.55            ( r1_tarski @
% 0.18/0.55              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.18/0.55              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.18/0.55    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.18/0.55  thf('0', plain,
% 0.18/0.55      (~ (r1_tarski @ 
% 0.18/0.55          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.18/0.55          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.18/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.55  thf('1', plain,
% 0.18/0.55      ((m1_subset_1 @ sk_D @ 
% 0.18/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.18/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.55  thf(redefinition_k7_relset_1, axiom,
% 0.18/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.55       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.18/0.55  thf('2', plain,
% 0.18/0.55      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.18/0.55         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.18/0.55          | ((k7_relset_1 @ X39 @ X40 @ X38 @ X41) = (k9_relat_1 @ X38 @ X41)))),
% 0.18/0.55      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.18/0.55  thf('3', plain,
% 0.18/0.55      (![X0 : $i]:
% 0.18/0.55         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.18/0.55           = (k9_relat_1 @ sk_D @ X0))),
% 0.18/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.55  thf('4', plain,
% 0.18/0.55      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.18/0.55          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.18/0.55      inference('demod', [status(thm)], ['0', '3'])).
% 0.18/0.55  thf(d10_xboole_0, axiom,
% 0.18/0.55    (![A:$i,B:$i]:
% 0.18/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.55  thf('5', plain,
% 0.18/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.18/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.55  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.18/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.18/0.55  thf('7', plain,
% 0.18/0.55      ((m1_subset_1 @ sk_D @ 
% 0.18/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.18/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.55  thf(t14_relset_1, axiom,
% 0.18/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.18/0.55       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.18/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.18/0.55  thf('8', plain,
% 0.18/0.55      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.18/0.55         (~ (r1_tarski @ (k2_relat_1 @ X42) @ X43)
% 0.18/0.55          | (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.18/0.55          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.18/0.55      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.18/0.55  thf('9', plain,
% 0.18/0.55      (![X0 : $i]:
% 0.18/0.55         ((m1_subset_1 @ sk_D @ 
% 0.18/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ X0)))
% 0.18/0.55          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.18/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.55  thf('10', plain,
% 0.18/0.55      ((m1_subset_1 @ sk_D @ 
% 0.18/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D))))),
% 0.18/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.18/0.55  thf(t3_subset, axiom,
% 0.18/0.55    (![A:$i,B:$i]:
% 0.18/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.55  thf('11', plain,
% 0.18/0.55      (![X16 : $i, X17 : $i]:
% 0.18/0.55         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.18/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.55  thf('12', plain,
% 0.18/0.55      ((r1_tarski @ sk_D @ 
% 0.18/0.55        (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D)))),
% 0.18/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.18/0.55  thf('13', plain,
% 0.18/0.55      (![X0 : $i, X2 : $i]:
% 0.18/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.18/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.55  thf('14', plain,
% 0.18/0.55      ((~ (r1_tarski @ 
% 0.18/0.55           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D)) @ sk_D)
% 0.18/0.55        | ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D)) = (sk_D)))),
% 0.18/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.55  thf(t144_relat_1, axiom,
% 0.18/0.55    (![A:$i,B:$i]:
% 0.18/0.55     ( ( v1_relat_1 @ B ) =>
% 0.18/0.55       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.18/0.55  thf('15', plain,
% 0.18/0.55      (![X21 : $i, X22 : $i]:
% 0.18/0.55         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ (k2_relat_1 @ X21))
% 0.18/0.55          | ~ (v1_relat_1 @ X21))),
% 0.18/0.55      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.18/0.55  thf('16', plain,
% 0.18/0.55      ((m1_subset_1 @ sk_D @ 
% 0.18/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.18/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.55  thf(dt_k1_relset_1, axiom,
% 0.18/0.55    (![A:$i,B:$i,C:$i]:
% 0.18/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.55       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.18/0.55  thf('17', plain,
% 0.18/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.18/0.55         ((m1_subset_1 @ (k1_relset_1 @ X32 @ X33 @ X34) @ (k1_zfmisc_1 @ X32))
% 0.18/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.18/0.55      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.18/0.55  thf('18', plain,
% 0.18/0.55      ((m1_subset_1 @ (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) @ 
% 0.18/0.55        (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.18/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.18/0.55  thf('19', plain,
% 0.18/0.55      ((m1_subset_1 @ sk_D @ 
% 0.18/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.18/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.18/0.55    (![A:$i,B:$i,C:$i]:
% 0.18/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.18/0.55  thf('20', plain,
% 0.18/0.55      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.18/0.55         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.18/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.18/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.18/0.55  thf('21', plain,
% 0.18/0.55      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.18/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.18/0.55  thf('22', plain,
% 0.18/0.55      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.18/0.55      inference('demod', [status(thm)], ['18', '21'])).
% 0.18/0.55  thf('23', plain,
% 0.18/0.55      (![X16 : $i, X17 : $i]:
% 0.18/0.55         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.18/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.55  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.18/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.18/0.55  thf(l3_zfmisc_1, axiom,
% 0.18/0.55    (![A:$i,B:$i]:
% 0.18/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.18/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.18/0.55  thf('25', plain,
% 0.18/0.55      (![X10 : $i, X11 : $i]:
% 0.18/0.55         (((X11) = (k1_tarski @ X10))
% 0.18/0.55          | ((X11) = (k1_xboole_0))
% 0.18/0.55          | ~ (r1_tarski @ X11 @ (k1_tarski @ X10)))),
% 0.18/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.18/0.55  thf('26', plain,
% 0.18/0.55      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.18/0.55        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.18/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.18/0.55  thf(t14_funct_1, axiom,
% 0.18/0.55    (![A:$i,B:$i]:
% 0.18/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.18/0.55       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.18/0.55         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.18/0.55  thf('27', plain,
% 0.18/0.55      (![X24 : $i, X25 : $i]:
% 0.18/0.55         (((k1_relat_1 @ X25) != (k1_tarski @ X24))
% 0.18/0.55          | ((k2_relat_1 @ X25) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 0.18/0.55          | ~ (v1_funct_1 @ X25)
% 0.18/0.55          | ~ (v1_relat_1 @ X25))),
% 0.18/0.55      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.18/0.55  thf('28', plain,
% 0.18/0.55      (![X0 : $i]:
% 0.18/0.55         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.18/0.55          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.18/0.55          | ~ (v1_relat_1 @ X0)
% 0.18/0.55          | ~ (v1_funct_1 @ X0)
% 0.18/0.55          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.18/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.18/0.55  thf('29', plain,
% 0.18/0.55      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.18/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.18/0.55        | ~ (v1_relat_1 @ sk_D)
% 0.18/0.55        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.55      inference('eq_res', [status(thm)], ['28'])).
% 0.18/0.55  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.18/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.55  thf('31', plain,
% 0.18/0.55      ((m1_subset_1 @ sk_D @ 
% 0.18/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.18/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.55  thf(cc1_relset_1, axiom,
% 0.18/0.55    (![A:$i,B:$i,C:$i]:
% 0.18/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.55       ( v1_relat_1 @ C ) ))).
% 0.18/0.55  thf('32', plain,
% 0.18/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.18/0.55         ((v1_relat_1 @ X26)
% 0.18/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.18/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.18/0.55  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.18/0.55  thf('34', plain,
% 0.18/0.55      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.18/0.55        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.55      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.18/0.55  thf('35', plain,
% 0.18/0.55      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.18/0.55          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.18/0.55      inference('demod', [status(thm)], ['0', '3'])).
% 0.18/0.55  thf('36', plain,
% 0.18/0.55      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.18/0.55        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.55  thf('37', plain,
% 0.18/0.55      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.55      inference('sup-', [status(thm)], ['15', '36'])).
% 0.18/0.55  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.18/0.55  thf('39', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.18/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.18/0.55  thf(t65_relat_1, axiom,
% 0.18/0.55    (![A:$i]:
% 0.18/0.55     ( ( v1_relat_1 @ A ) =>
% 0.18/0.55       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.55         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.18/0.55  thf('40', plain,
% 0.18/0.55      (![X23 : $i]:
% 0.18/0.55         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.18/0.55          | ((k2_relat_1 @ X23) = (k1_xboole_0))
% 0.18/0.55          | ~ (v1_relat_1 @ X23))),
% 0.18/0.55      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.18/0.55  thf('41', plain,
% 0.18/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.55        | ~ (v1_relat_1 @ sk_D)
% 0.18/0.55        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.18/0.55  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.18/0.55  thf('43', plain,
% 0.18/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.55        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.18/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.18/0.55  thf('44', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.18/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.18/0.55  thf(t113_zfmisc_1, axiom,
% 0.18/0.55    (![A:$i,B:$i]:
% 0.18/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.18/0.55  thf('45', plain,
% 0.18/0.55      (![X14 : $i, X15 : $i]:
% 0.18/0.55         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.18/0.55          | ((X15) != (k1_xboole_0)))),
% 0.18/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.18/0.55  thf('46', plain,
% 0.18/0.55      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.18/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.55  thf('47', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.18/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.55  thf('48', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.18/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.18/0.55  thf('49', plain,
% 0.18/0.55      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.18/0.55  thf('50', plain, (((k1_xboole_0) = (sk_D))),
% 0.18/0.55      inference('demod', [status(thm)], ['14', '44', '46', '47', '48', '49'])).
% 0.18/0.55  thf('51', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.18/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.55  thf('52', plain,
% 0.18/0.55      (![X16 : $i, X18 : $i]:
% 0.18/0.55         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.18/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.18/0.55  thf('53', plain,
% 0.18/0.55      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.18/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.18/0.55  thf(cc2_relset_1, axiom,
% 0.18/0.55    (![A:$i,B:$i,C:$i]:
% 0.18/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.18/0.55  thf('54', plain,
% 0.18/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.18/0.55         ((v5_relat_1 @ X29 @ X31)
% 0.18/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.18/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.18/0.55  thf('55', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.18/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.18/0.55  thf(d19_relat_1, axiom,
% 0.18/0.55    (![A:$i,B:$i]:
% 0.18/0.55     ( ( v1_relat_1 @ B ) =>
% 0.18/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.18/0.55  thf('56', plain,
% 0.18/0.55      (![X19 : $i, X20 : $i]:
% 0.18/0.55         (~ (v5_relat_1 @ X19 @ X20)
% 0.18/0.55          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.18/0.55          | ~ (v1_relat_1 @ X19))),
% 0.18/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.18/0.55  thf('57', plain,
% 0.18/0.55      (![X0 : $i]:
% 0.18/0.55         (~ (v1_relat_1 @ k1_xboole_0)
% 0.18/0.55          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.18/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.18/0.55  thf('58', plain,
% 0.18/0.55      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.18/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.18/0.55  thf('59', plain,
% 0.18/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.18/0.55         ((v1_relat_1 @ X26)
% 0.18/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.18/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.18/0.55  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.18/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.18/0.55  thf('61', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.18/0.55      inference('demod', [status(thm)], ['57', '60'])).
% 0.18/0.55  thf('62', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.18/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.55  thf('63', plain,
% 0.18/0.55      (![X0 : $i, X2 : $i]:
% 0.18/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.18/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.55  thf('64', plain,
% 0.18/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.18/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.18/0.55  thf('65', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.55      inference('sup-', [status(thm)], ['61', '64'])).
% 0.18/0.55  thf('66', plain,
% 0.18/0.55      (![X21 : $i, X22 : $i]:
% 0.18/0.55         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ (k2_relat_1 @ X21))
% 0.18/0.55          | ~ (v1_relat_1 @ X21))),
% 0.18/0.55      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.18/0.55  thf('67', plain,
% 0.18/0.55      (![X0 : $i]:
% 0.18/0.55         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.18/0.55          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.18/0.55      inference('sup+', [status(thm)], ['65', '66'])).
% 0.18/0.55  thf('68', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.18/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.18/0.55  thf('69', plain,
% 0.18/0.55      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.18/0.55      inference('demod', [status(thm)], ['67', '68'])).
% 0.18/0.55  thf('70', plain,
% 0.18/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.18/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.18/0.55  thf('71', plain,
% 0.18/0.55      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.18/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.18/0.55  thf('72', plain, (((k1_xboole_0) = (sk_D))),
% 0.18/0.55      inference('demod', [status(thm)], ['14', '44', '46', '47', '48', '49'])).
% 0.18/0.55  thf('73', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.18/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.55  thf('74', plain, ($false),
% 0.18/0.55      inference('demod', [status(thm)], ['4', '50', '71', '72', '73'])).
% 0.18/0.55  
% 0.18/0.55  % SZS output end Refutation
% 0.18/0.55  
% 0.18/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
