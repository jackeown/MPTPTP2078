%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3CjiZUaM5X

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:19 EST 2020

% Result     : Theorem 4.16s
% Output     : Refutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 591 expanded)
%              Number of leaves         :   48 ( 190 expanded)
%              Depth                    :   20
%              Number of atoms          : 1472 (10420 expanded)
%              Number of equality atoms :   52 ( 139 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
      = ( k5_relat_1 @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
    = ( k5_relat_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('13',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('16',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('17',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('21',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X1 @ X0 @ sk_C @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['8','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
    = ( k5_relat_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('44',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( $true
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('49',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('70',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('74',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['58','59','74'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('76',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('80',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('81',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('84',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('85',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['83','84'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('89',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('91',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('92',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['58','59','74'])).

thf('95',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['79','82','93','94','95','96','101'])).

thf('103',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('104',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('106',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('107',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['102','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('112',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('114',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('116',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['55','116'])).

thf('118',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','117'])).

thf('119',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('121',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('122',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['118','123'])).

thf('125',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('127',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48 ) )
      | ( v2_funct_1 @ X52 )
      | ( X50 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X49 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133','134','135','136'])).

thf('138',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['53'])).

thf('139',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['114','115'])).

thf('140',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['138','139'])).

thf('141',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['137','140'])).

thf('142',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','23'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['124','141','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3CjiZUaM5X
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:28:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.16/4.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.16/4.37  % Solved by: fo/fo7.sh
% 4.16/4.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.16/4.37  % done 3565 iterations in 3.943s
% 4.16/4.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.16/4.37  % SZS output start Refutation
% 4.16/4.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.16/4.37  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.16/4.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.16/4.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.16/4.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.16/4.37  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.16/4.37  thf(sk_C_type, type, sk_C: $i).
% 4.16/4.37  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.16/4.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.16/4.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.16/4.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.16/4.37  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.16/4.37  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.16/4.37  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.16/4.37  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.16/4.37  thf(sk_D_type, type, sk_D: $i).
% 4.16/4.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.16/4.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.16/4.37  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.16/4.37  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.16/4.37  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.16/4.37  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.16/4.37  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.16/4.37  thf(sk_B_type, type, sk_B: $i).
% 4.16/4.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.16/4.37  thf(sk_A_type, type, sk_A: $i).
% 4.16/4.37  thf(t29_funct_2, conjecture,
% 4.16/4.37    (![A:$i,B:$i,C:$i]:
% 4.16/4.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.16/4.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.16/4.37       ( ![D:$i]:
% 4.16/4.37         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.16/4.37             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.16/4.37           ( ( r2_relset_1 @
% 4.16/4.37               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.16/4.37               ( k6_partfun1 @ A ) ) =>
% 4.16/4.37             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.16/4.37  thf(zf_stmt_0, negated_conjecture,
% 4.16/4.37    (~( ![A:$i,B:$i,C:$i]:
% 4.16/4.37        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.16/4.37            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.16/4.37          ( ![D:$i]:
% 4.16/4.37            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.16/4.37                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.16/4.37              ( ( r2_relset_1 @
% 4.16/4.37                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.16/4.37                  ( k6_partfun1 @ A ) ) =>
% 4.16/4.37                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.16/4.37    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.16/4.37  thf('0', plain,
% 4.16/4.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.16/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.37  thf('1', plain,
% 4.16/4.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.16/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.37  thf(redefinition_k1_partfun1, axiom,
% 4.16/4.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.16/4.37     ( ( ( v1_funct_1 @ E ) & 
% 4.16/4.37         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.16/4.37         ( v1_funct_1 @ F ) & 
% 4.16/4.37         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.16/4.37       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.16/4.37  thf('2', plain,
% 4.16/4.37      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.16/4.37         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 4.16/4.37          | ~ (v1_funct_1 @ X41)
% 4.16/4.37          | ~ (v1_funct_1 @ X44)
% 4.16/4.37          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 4.16/4.37          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 4.16/4.37              = (k5_relat_1 @ X41 @ X44)))),
% 4.16/4.37      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.16/4.37  thf('3', plain,
% 4.16/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.37         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.16/4.37            = (k5_relat_1 @ sk_C @ X0))
% 4.16/4.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.16/4.37          | ~ (v1_funct_1 @ X0)
% 4.16/4.37          | ~ (v1_funct_1 @ sk_C))),
% 4.16/4.37      inference('sup-', [status(thm)], ['1', '2'])).
% 4.16/4.37  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.37  thf('5', plain,
% 4.16/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.37         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.16/4.37            = (k5_relat_1 @ sk_C @ X0))
% 4.16/4.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.16/4.37          | ~ (v1_funct_1 @ X0))),
% 4.16/4.37      inference('demod', [status(thm)], ['3', '4'])).
% 4.16/4.37  thf('6', plain,
% 4.16/4.37      ((~ (v1_funct_1 @ sk_C)
% 4.16/4.37        | ((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 4.16/4.37            = (k5_relat_1 @ sk_C @ sk_C)))),
% 4.16/4.37      inference('sup-', [status(thm)], ['0', '5'])).
% 4.16/4.37  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.37  thf('8', plain,
% 4.16/4.37      (((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 4.16/4.37         = (k5_relat_1 @ sk_C @ sk_C))),
% 4.16/4.37      inference('demod', [status(thm)], ['6', '7'])).
% 4.16/4.37  thf(l13_xboole_0, axiom,
% 4.16/4.37    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.16/4.37  thf('9', plain,
% 4.16/4.37      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.16/4.37      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.16/4.37  thf(fc4_zfmisc_1, axiom,
% 4.16/4.37    (![A:$i,B:$i]:
% 4.16/4.37     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.16/4.37  thf('10', plain,
% 4.16/4.37      (![X8 : $i, X9 : $i]:
% 4.16/4.37         (~ (v1_xboole_0 @ X8) | (v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 4.16/4.37      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.16/4.37  thf('11', plain,
% 4.16/4.37      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.16/4.37      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.16/4.37  thf('12', plain,
% 4.16/4.37      (![X0 : $i, X1 : $i]:
% 4.16/4.37         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 4.16/4.37      inference('sup-', [status(thm)], ['10', '11'])).
% 4.16/4.37  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 4.16/4.37  thf('13', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.16/4.37      inference('cnf', [status(esa)], [t81_relat_1])).
% 4.16/4.37  thf(redefinition_k6_partfun1, axiom,
% 4.16/4.37    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.16/4.37  thf('14', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 4.16/4.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.16/4.37  thf('15', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.16/4.37      inference('demod', [status(thm)], ['13', '14'])).
% 4.16/4.37  thf(dt_k6_partfun1, axiom,
% 4.16/4.37    (![A:$i]:
% 4.16/4.37     ( ( m1_subset_1 @
% 4.16/4.37         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.16/4.37       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.16/4.37  thf('16', plain,
% 4.16/4.37      (![X40 : $i]:
% 4.16/4.37         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 4.16/4.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 4.16/4.37      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.16/4.37  thf('17', plain,
% 4.16/4.37      ((m1_subset_1 @ k1_xboole_0 @ 
% 4.16/4.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 4.16/4.37      inference('sup+', [status(thm)], ['15', '16'])).
% 4.16/4.37  thf('18', plain,
% 4.16/4.37      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.16/4.37        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.16/4.37      inference('sup+', [status(thm)], ['12', '17'])).
% 4.16/4.37  thf(d10_xboole_0, axiom,
% 4.16/4.37    (![A:$i,B:$i]:
% 4.16/4.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.16/4.37  thf('19', plain,
% 4.16/4.37      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 4.16/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.16/4.37  thf('20', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 4.16/4.37      inference('simplify', [status(thm)], ['19'])).
% 4.16/4.37  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 4.16/4.37  thf('21', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 4.16/4.37      inference('cnf', [status(esa)], [t65_xboole_1])).
% 4.16/4.37  thf(t69_xboole_1, axiom,
% 4.16/4.37    (![A:$i,B:$i]:
% 4.16/4.37     ( ( ~( v1_xboole_0 @ B ) ) =>
% 4.16/4.37       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 4.16/4.37  thf('22', plain,
% 4.16/4.37      (![X6 : $i, X7 : $i]:
% 4.16/4.37         (~ (r1_xboole_0 @ X6 @ X7)
% 4.16/4.37          | ~ (r1_tarski @ X6 @ X7)
% 4.16/4.37          | (v1_xboole_0 @ X6))),
% 4.16/4.37      inference('cnf', [status(esa)], [t69_xboole_1])).
% 4.16/4.37  thf('23', plain,
% 4.16/4.37      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.16/4.37      inference('sup-', [status(thm)], ['21', '22'])).
% 4.16/4.37  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.16/4.37      inference('sup-', [status(thm)], ['20', '23'])).
% 4.16/4.37  thf('25', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.16/4.37      inference('demod', [status(thm)], ['18', '24'])).
% 4.16/4.37  thf('26', plain,
% 4.16/4.37      (![X0 : $i]:
% 4.16/4.37         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.16/4.37          | ~ (v1_xboole_0 @ X0))),
% 4.16/4.37      inference('sup+', [status(thm)], ['9', '25'])).
% 4.16/4.37  thf('27', plain,
% 4.16/4.37      (![X0 : $i, X1 : $i]:
% 4.16/4.37         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 4.16/4.37      inference('sup-', [status(thm)], ['10', '11'])).
% 4.16/4.37  thf('28', plain,
% 4.16/4.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.16/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.37  thf(dt_k1_partfun1, axiom,
% 4.16/4.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.16/4.37     ( ( ( v1_funct_1 @ E ) & 
% 4.16/4.37         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.16/4.37         ( v1_funct_1 @ F ) & 
% 4.16/4.37         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.16/4.37       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.16/4.37         ( m1_subset_1 @
% 4.16/4.37           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.16/4.37           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.16/4.37  thf('29', plain,
% 4.16/4.37      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 4.16/4.37         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 4.16/4.37          | ~ (v1_funct_1 @ X33)
% 4.16/4.37          | ~ (v1_funct_1 @ X36)
% 4.16/4.37          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 4.16/4.37          | (v1_funct_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)))),
% 4.16/4.37      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.16/4.37  thf('30', plain,
% 4.16/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.37         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 4.16/4.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.16/4.37          | ~ (v1_funct_1 @ X0)
% 4.16/4.37          | ~ (v1_funct_1 @ sk_C))),
% 4.16/4.37      inference('sup-', [status(thm)], ['28', '29'])).
% 4.16/4.37  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('32', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 4.16/4.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.16/4.38          | ~ (v1_funct_1 @ X0))),
% 4.16/4.38      inference('demod', [status(thm)], ['30', '31'])).
% 4.16/4.38  thf('33', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.16/4.38          | ~ (v1_xboole_0 @ X1)
% 4.16/4.38          | ~ (v1_funct_1 @ X2)
% 4.16/4.38          | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X1 @ X0 @ sk_C @ X2)))),
% 4.16/4.38      inference('sup-', [status(thm)], ['27', '32'])).
% 4.16/4.38  thf('34', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         (~ (v1_xboole_0 @ X0)
% 4.16/4.38          | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 4.16/4.38          | ~ (v1_funct_1 @ X0)
% 4.16/4.38          | ~ (v1_xboole_0 @ X2))),
% 4.16/4.38      inference('sup-', [status(thm)], ['26', '33'])).
% 4.16/4.38  thf('35', plain,
% 4.16/4.38      (((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))
% 4.16/4.38        | ~ (v1_xboole_0 @ sk_A)
% 4.16/4.38        | ~ (v1_funct_1 @ sk_C)
% 4.16/4.38        | ~ (v1_xboole_0 @ sk_C))),
% 4.16/4.38      inference('sup+', [status(thm)], ['8', '34'])).
% 4.16/4.38  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('37', plain,
% 4.16/4.38      (((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))
% 4.16/4.38        | ~ (v1_xboole_0 @ sk_A)
% 4.16/4.38        | ~ (v1_xboole_0 @ sk_C))),
% 4.16/4.38      inference('demod', [status(thm)], ['35', '36'])).
% 4.16/4.38  thf('38', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('39', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 4.16/4.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.16/4.38          | ~ (v1_funct_1 @ X0))),
% 4.16/4.38      inference('demod', [status(thm)], ['30', '31'])).
% 4.16/4.38  thf('40', plain,
% 4.16/4.38      ((~ (v1_funct_1 @ sk_C)
% 4.16/4.38        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)))),
% 4.16/4.38      inference('sup-', [status(thm)], ['38', '39'])).
% 4.16/4.38  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('42', plain,
% 4.16/4.38      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C))),
% 4.16/4.38      inference('demod', [status(thm)], ['40', '41'])).
% 4.16/4.38  thf('43', plain,
% 4.16/4.38      (((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 4.16/4.38         = (k5_relat_1 @ sk_C @ sk_C))),
% 4.16/4.38      inference('demod', [status(thm)], ['6', '7'])).
% 4.16/4.38  thf('44', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))),
% 4.16/4.38      inference('demod', [status(thm)], ['42', '43'])).
% 4.16/4.38  thf('45', plain, (($true | ~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C))),
% 4.16/4.38      inference('demod', [status(thm)], ['37', '44'])).
% 4.16/4.38  thf('46', plain,
% 4.16/4.38      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.16/4.38      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.16/4.38  thf('47', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.16/4.38      inference('demod', [status(thm)], ['13', '14'])).
% 4.16/4.38  thf(fc4_funct_1, axiom,
% 4.16/4.38    (![A:$i]:
% 4.16/4.38     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.16/4.38       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.16/4.38  thf('48', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 4.16/4.38      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.16/4.38  thf('49', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 4.16/4.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.16/4.38  thf('50', plain, (![X23 : $i]: (v2_funct_1 @ (k6_partfun1 @ X23))),
% 4.16/4.38      inference('demod', [status(thm)], ['48', '49'])).
% 4.16/4.38  thf('51', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.16/4.38      inference('sup+', [status(thm)], ['47', '50'])).
% 4.16/4.38  thf('52', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 4.16/4.38      inference('sup+', [status(thm)], ['46', '51'])).
% 4.16/4.38  thf('53', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('54', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.16/4.38      inference('split', [status(esa)], ['53'])).
% 4.16/4.38  thf('55', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.16/4.38      inference('sup-', [status(thm)], ['52', '54'])).
% 4.16/4.38  thf('56', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('57', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.16/4.38            = (k5_relat_1 @ sk_C @ X0))
% 4.16/4.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.16/4.38          | ~ (v1_funct_1 @ X0))),
% 4.16/4.38      inference('demod', [status(thm)], ['3', '4'])).
% 4.16/4.38  thf('58', plain,
% 4.16/4.38      ((~ (v1_funct_1 @ sk_D)
% 4.16/4.38        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.16/4.38            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.16/4.38      inference('sup-', [status(thm)], ['56', '57'])).
% 4.16/4.38  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('60', plain,
% 4.16/4.38      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.16/4.38        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.16/4.38        (k6_partfun1 @ sk_A))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('61', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('62', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('63', plain,
% 4.16/4.38      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 4.16/4.38         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 4.16/4.38          | ~ (v1_funct_1 @ X33)
% 4.16/4.38          | ~ (v1_funct_1 @ X36)
% 4.16/4.38          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 4.16/4.38          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 4.16/4.38             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 4.16/4.38      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.16/4.38  thf('64', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.16/4.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.16/4.38          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.16/4.38          | ~ (v1_funct_1 @ X1)
% 4.16/4.38          | ~ (v1_funct_1 @ sk_C))),
% 4.16/4.38      inference('sup-', [status(thm)], ['62', '63'])).
% 4.16/4.38  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('66', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.16/4.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.16/4.38          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.16/4.38          | ~ (v1_funct_1 @ X1))),
% 4.16/4.38      inference('demod', [status(thm)], ['64', '65'])).
% 4.16/4.38  thf('67', plain,
% 4.16/4.38      ((~ (v1_funct_1 @ sk_D)
% 4.16/4.38        | (m1_subset_1 @ 
% 4.16/4.38           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.16/4.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.16/4.38      inference('sup-', [status(thm)], ['61', '66'])).
% 4.16/4.38  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('69', plain,
% 4.16/4.38      ((m1_subset_1 @ 
% 4.16/4.38        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.16/4.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.16/4.38      inference('demod', [status(thm)], ['67', '68'])).
% 4.16/4.38  thf(redefinition_r2_relset_1, axiom,
% 4.16/4.38    (![A:$i,B:$i,C:$i,D:$i]:
% 4.16/4.38     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.16/4.38         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.16/4.38       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.16/4.38  thf('70', plain,
% 4.16/4.38      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 4.16/4.38         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.16/4.38          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.16/4.38          | ((X27) = (X30))
% 4.16/4.38          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 4.16/4.38      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.16/4.38  thf('71', plain,
% 4.16/4.38      (![X0 : $i]:
% 4.16/4.38         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.16/4.38             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 4.16/4.38          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 4.16/4.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.16/4.38      inference('sup-', [status(thm)], ['69', '70'])).
% 4.16/4.38  thf('72', plain,
% 4.16/4.38      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.16/4.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.16/4.38        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.16/4.38            = (k6_partfun1 @ sk_A)))),
% 4.16/4.38      inference('sup-', [status(thm)], ['60', '71'])).
% 4.16/4.38  thf('73', plain,
% 4.16/4.38      (![X40 : $i]:
% 4.16/4.38         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 4.16/4.38          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 4.16/4.38      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.16/4.38  thf('74', plain,
% 4.16/4.38      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.16/4.38         = (k6_partfun1 @ sk_A))),
% 4.16/4.38      inference('demod', [status(thm)], ['72', '73'])).
% 4.16/4.38  thf('75', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 4.16/4.38      inference('demod', [status(thm)], ['58', '59', '74'])).
% 4.16/4.38  thf(t45_relat_1, axiom,
% 4.16/4.38    (![A:$i]:
% 4.16/4.38     ( ( v1_relat_1 @ A ) =>
% 4.16/4.38       ( ![B:$i]:
% 4.16/4.38         ( ( v1_relat_1 @ B ) =>
% 4.16/4.38           ( r1_tarski @
% 4.16/4.38             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 4.16/4.38  thf('76', plain,
% 4.16/4.38      (![X18 : $i, X19 : $i]:
% 4.16/4.38         (~ (v1_relat_1 @ X18)
% 4.16/4.38          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X19 @ X18)) @ 
% 4.16/4.38             (k2_relat_1 @ X18))
% 4.16/4.38          | ~ (v1_relat_1 @ X19))),
% 4.16/4.38      inference('cnf', [status(esa)], [t45_relat_1])).
% 4.16/4.38  thf('77', plain,
% 4.16/4.38      (![X1 : $i, X3 : $i]:
% 4.16/4.38         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 4.16/4.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.16/4.38  thf('78', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i]:
% 4.16/4.38         (~ (v1_relat_1 @ X1)
% 4.16/4.38          | ~ (v1_relat_1 @ X0)
% 4.16/4.38          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 4.16/4.38               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 4.16/4.38          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 4.16/4.38      inference('sup-', [status(thm)], ['76', '77'])).
% 4.16/4.38  thf('79', plain,
% 4.16/4.38      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 4.16/4.38           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 4.16/4.38        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 4.16/4.38        | ~ (v1_relat_1 @ sk_D)
% 4.16/4.38        | ~ (v1_relat_1 @ sk_C))),
% 4.16/4.38      inference('sup-', [status(thm)], ['75', '78'])).
% 4.16/4.38  thf(t71_relat_1, axiom,
% 4.16/4.38    (![A:$i]:
% 4.16/4.38     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.16/4.38       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.16/4.38  thf('80', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 4.16/4.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.16/4.38  thf('81', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 4.16/4.38      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.16/4.38  thf('82', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 4.16/4.38      inference('demod', [status(thm)], ['80', '81'])).
% 4.16/4.38  thf('83', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf(cc2_relset_1, axiom,
% 4.16/4.38    (![A:$i,B:$i,C:$i]:
% 4.16/4.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.38       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.16/4.38  thf('84', plain,
% 4.16/4.38      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.16/4.38         ((v5_relat_1 @ X24 @ X26)
% 4.16/4.38          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.16/4.38      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.16/4.38  thf('85', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.16/4.38      inference('sup-', [status(thm)], ['83', '84'])).
% 4.16/4.38  thf(d19_relat_1, axiom,
% 4.16/4.38    (![A:$i,B:$i]:
% 4.16/4.38     ( ( v1_relat_1 @ B ) =>
% 4.16/4.38       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.16/4.38  thf('86', plain,
% 4.16/4.38      (![X14 : $i, X15 : $i]:
% 4.16/4.38         (~ (v5_relat_1 @ X14 @ X15)
% 4.16/4.38          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 4.16/4.38          | ~ (v1_relat_1 @ X14))),
% 4.16/4.38      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.16/4.38  thf('87', plain,
% 4.16/4.38      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 4.16/4.38      inference('sup-', [status(thm)], ['85', '86'])).
% 4.16/4.38  thf('88', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf(cc2_relat_1, axiom,
% 4.16/4.38    (![A:$i]:
% 4.16/4.38     ( ( v1_relat_1 @ A ) =>
% 4.16/4.38       ( ![B:$i]:
% 4.16/4.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.16/4.38  thf('89', plain,
% 4.16/4.38      (![X12 : $i, X13 : $i]:
% 4.16/4.38         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.16/4.38          | (v1_relat_1 @ X12)
% 4.16/4.38          | ~ (v1_relat_1 @ X13))),
% 4.16/4.38      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.16/4.38  thf('90', plain,
% 4.16/4.38      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 4.16/4.38      inference('sup-', [status(thm)], ['88', '89'])).
% 4.16/4.38  thf(fc6_relat_1, axiom,
% 4.16/4.38    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.16/4.38  thf('91', plain,
% 4.16/4.38      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 4.16/4.38      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.16/4.38  thf('92', plain, ((v1_relat_1 @ sk_D)),
% 4.16/4.38      inference('demod', [status(thm)], ['90', '91'])).
% 4.16/4.38  thf('93', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 4.16/4.38      inference('demod', [status(thm)], ['87', '92'])).
% 4.16/4.38  thf('94', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 4.16/4.38      inference('demod', [status(thm)], ['58', '59', '74'])).
% 4.16/4.38  thf('95', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 4.16/4.38      inference('demod', [status(thm)], ['80', '81'])).
% 4.16/4.38  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 4.16/4.38      inference('demod', [status(thm)], ['90', '91'])).
% 4.16/4.38  thf('97', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('98', plain,
% 4.16/4.38      (![X12 : $i, X13 : $i]:
% 4.16/4.38         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.16/4.38          | (v1_relat_1 @ X12)
% 4.16/4.38          | ~ (v1_relat_1 @ X13))),
% 4.16/4.38      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.16/4.38  thf('99', plain,
% 4.16/4.38      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 4.16/4.38      inference('sup-', [status(thm)], ['97', '98'])).
% 4.16/4.38  thf('100', plain,
% 4.16/4.38      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 4.16/4.38      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.16/4.38  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 4.16/4.38      inference('demod', [status(thm)], ['99', '100'])).
% 4.16/4.38  thf('102', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.16/4.38      inference('demod', [status(thm)],
% 4.16/4.38                ['79', '82', '93', '94', '95', '96', '101'])).
% 4.16/4.38  thf('103', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 4.16/4.38      inference('simplify', [status(thm)], ['19'])).
% 4.16/4.38  thf('104', plain,
% 4.16/4.38      (![X14 : $i, X15 : $i]:
% 4.16/4.38         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 4.16/4.38          | (v5_relat_1 @ X14 @ X15)
% 4.16/4.38          | ~ (v1_relat_1 @ X14))),
% 4.16/4.38      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.16/4.38  thf('105', plain,
% 4.16/4.38      (![X0 : $i]:
% 4.16/4.38         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.16/4.38      inference('sup-', [status(thm)], ['103', '104'])).
% 4.16/4.38  thf(d3_funct_2, axiom,
% 4.16/4.38    (![A:$i,B:$i]:
% 4.16/4.38     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.16/4.38       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.16/4.38  thf('106', plain,
% 4.16/4.38      (![X31 : $i, X32 : $i]:
% 4.16/4.38         (((k2_relat_1 @ X32) != (X31))
% 4.16/4.38          | (v2_funct_2 @ X32 @ X31)
% 4.16/4.38          | ~ (v5_relat_1 @ X32 @ X31)
% 4.16/4.38          | ~ (v1_relat_1 @ X32))),
% 4.16/4.38      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.16/4.38  thf('107', plain,
% 4.16/4.38      (![X32 : $i]:
% 4.16/4.38         (~ (v1_relat_1 @ X32)
% 4.16/4.38          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 4.16/4.38          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 4.16/4.38      inference('simplify', [status(thm)], ['106'])).
% 4.16/4.38  thf('108', plain,
% 4.16/4.38      (![X0 : $i]:
% 4.16/4.38         (~ (v1_relat_1 @ X0)
% 4.16/4.38          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 4.16/4.38          | ~ (v1_relat_1 @ X0))),
% 4.16/4.38      inference('sup-', [status(thm)], ['105', '107'])).
% 4.16/4.38  thf('109', plain,
% 4.16/4.38      (![X0 : $i]:
% 4.16/4.38         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.16/4.38      inference('simplify', [status(thm)], ['108'])).
% 4.16/4.38  thf('110', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.16/4.38      inference('sup+', [status(thm)], ['102', '109'])).
% 4.16/4.38  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 4.16/4.38      inference('demod', [status(thm)], ['90', '91'])).
% 4.16/4.38  thf('112', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.16/4.38      inference('demod', [status(thm)], ['110', '111'])).
% 4.16/4.38  thf('113', plain,
% 4.16/4.38      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.16/4.38      inference('split', [status(esa)], ['53'])).
% 4.16/4.38  thf('114', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 4.16/4.38      inference('sup-', [status(thm)], ['112', '113'])).
% 4.16/4.38  thf('115', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.16/4.38      inference('split', [status(esa)], ['53'])).
% 4.16/4.38  thf('116', plain, (~ ((v2_funct_1 @ sk_C))),
% 4.16/4.38      inference('sat_resolution*', [status(thm)], ['114', '115'])).
% 4.16/4.38  thf('117', plain, (~ (v1_xboole_0 @ sk_C)),
% 4.16/4.38      inference('simpl_trail', [status(thm)], ['55', '116'])).
% 4.16/4.38  thf('118', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 4.16/4.38      inference('clc', [status(thm)], ['45', '117'])).
% 4.16/4.38  thf('119', plain,
% 4.16/4.38      (![X8 : $i, X9 : $i]:
% 4.16/4.38         (~ (v1_xboole_0 @ X8) | (v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 4.16/4.38      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.16/4.38  thf('120', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf(cc1_subset_1, axiom,
% 4.16/4.38    (![A:$i]:
% 4.16/4.38     ( ( v1_xboole_0 @ A ) =>
% 4.16/4.38       ( ![B:$i]:
% 4.16/4.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 4.16/4.38  thf('121', plain,
% 4.16/4.38      (![X10 : $i, X11 : $i]:
% 4.16/4.38         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 4.16/4.38          | (v1_xboole_0 @ X10)
% 4.16/4.38          | ~ (v1_xboole_0 @ X11))),
% 4.16/4.38      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.16/4.38  thf('122', plain,
% 4.16/4.38      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 4.16/4.38      inference('sup-', [status(thm)], ['120', '121'])).
% 4.16/4.38  thf('123', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 4.16/4.38      inference('sup-', [status(thm)], ['119', '122'])).
% 4.16/4.38  thf('124', plain, (~ (v1_xboole_0 @ sk_A)),
% 4.16/4.38      inference('clc', [status(thm)], ['118', '123'])).
% 4.16/4.38  thf('125', plain,
% 4.16/4.38      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.16/4.38         = (k6_partfun1 @ sk_A))),
% 4.16/4.38      inference('demod', [status(thm)], ['72', '73'])).
% 4.16/4.38  thf('126', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf(t26_funct_2, axiom,
% 4.16/4.38    (![A:$i,B:$i,C:$i,D:$i]:
% 4.16/4.38     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.16/4.38         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.16/4.38       ( ![E:$i]:
% 4.16/4.38         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.16/4.38             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.16/4.38           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.16/4.38             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.16/4.38               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.16/4.38  thf('127', plain,
% 4.16/4.38      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 4.16/4.38         (~ (v1_funct_1 @ X48)
% 4.16/4.38          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 4.16/4.38          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 4.16/4.38          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48))
% 4.16/4.38          | (v2_funct_1 @ X52)
% 4.16/4.38          | ((X50) = (k1_xboole_0))
% 4.16/4.38          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 4.16/4.38          | ~ (v1_funct_2 @ X52 @ X51 @ X49)
% 4.16/4.38          | ~ (v1_funct_1 @ X52))),
% 4.16/4.38      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.16/4.38  thf('128', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i]:
% 4.16/4.38         (~ (v1_funct_1 @ X0)
% 4.16/4.38          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.16/4.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.16/4.38          | ((sk_A) = (k1_xboole_0))
% 4.16/4.38          | (v2_funct_1 @ X0)
% 4.16/4.38          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.16/4.38          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.16/4.38          | ~ (v1_funct_1 @ sk_D))),
% 4.16/4.38      inference('sup-', [status(thm)], ['126', '127'])).
% 4.16/4.38  thf('129', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('130', plain, ((v1_funct_1 @ sk_D)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('131', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i]:
% 4.16/4.38         (~ (v1_funct_1 @ X0)
% 4.16/4.38          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.16/4.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.16/4.38          | ((sk_A) = (k1_xboole_0))
% 4.16/4.38          | (v2_funct_1 @ X0)
% 4.16/4.38          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 4.16/4.38      inference('demod', [status(thm)], ['128', '129', '130'])).
% 4.16/4.38  thf('132', plain,
% 4.16/4.38      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 4.16/4.38        | (v2_funct_1 @ sk_C)
% 4.16/4.38        | ((sk_A) = (k1_xboole_0))
% 4.16/4.38        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.16/4.38        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.16/4.38        | ~ (v1_funct_1 @ sk_C))),
% 4.16/4.38      inference('sup-', [status(thm)], ['125', '131'])).
% 4.16/4.38  thf('133', plain, (![X23 : $i]: (v2_funct_1 @ (k6_partfun1 @ X23))),
% 4.16/4.38      inference('demod', [status(thm)], ['48', '49'])).
% 4.16/4.38  thf('134', plain,
% 4.16/4.38      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('135', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf('137', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.16/4.38      inference('demod', [status(thm)], ['132', '133', '134', '135', '136'])).
% 4.16/4.38  thf('138', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.16/4.38      inference('split', [status(esa)], ['53'])).
% 4.16/4.38  thf('139', plain, (~ ((v2_funct_1 @ sk_C))),
% 4.16/4.38      inference('sat_resolution*', [status(thm)], ['114', '115'])).
% 4.16/4.38  thf('140', plain, (~ (v2_funct_1 @ sk_C)),
% 4.16/4.38      inference('simpl_trail', [status(thm)], ['138', '139'])).
% 4.16/4.38  thf('141', plain, (((sk_A) = (k1_xboole_0))),
% 4.16/4.38      inference('clc', [status(thm)], ['137', '140'])).
% 4.16/4.38  thf('142', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.16/4.38      inference('sup-', [status(thm)], ['20', '23'])).
% 4.16/4.38  thf('143', plain, ($false),
% 4.16/4.38      inference('demod', [status(thm)], ['124', '141', '142'])).
% 4.16/4.38  
% 4.16/4.38  % SZS output end Refutation
% 4.16/4.38  
% 4.16/4.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
