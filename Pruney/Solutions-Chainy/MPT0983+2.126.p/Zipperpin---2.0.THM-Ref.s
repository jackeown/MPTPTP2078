%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kah1l6ZGCD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:21 EST 2020

% Result     : Theorem 3.94s
% Output     : Refutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 608 expanded)
%              Number of leaves         :   47 ( 195 expanded)
%              Depth                    :   20
%              Number of atoms          : 1477 (10492 expanded)
%              Number of equality atoms :   53 ( 151 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
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
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('16',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('17',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('23',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X1 @ X0 @ sk_C @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['8','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C )
    = ( k5_relat_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('46',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( $true
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('50',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('51',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('72',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('76',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['60','61','76'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('78',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('79',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('82',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('83',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('84',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('86',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('87',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['85','86'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('91',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('93',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('94',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['60','61','76'])).

thf('97',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['92','93'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['81','84','95','96','97','98','103'])).

thf('105',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('106',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('108',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('109',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['104','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['92','93'])).

thf('114',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('116',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('118',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['57','118'])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','119'])).

thf('121',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('123',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('124',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['120','125'])).

thf('127',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('128',plain,(
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

thf('129',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X47 @ X47 @ X48 @ X50 @ X46 ) )
      | ( v2_funct_1 @ X50 )
      | ( X48 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X47 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['55'])).

thf('141',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('142',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['140','141'])).

thf('143',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['139','142'])).

thf('144',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','25'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['126','143','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kah1l6ZGCD
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.94/4.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.94/4.15  % Solved by: fo/fo7.sh
% 3.94/4.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.94/4.15  % done 3546 iterations in 3.684s
% 3.94/4.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.94/4.15  % SZS output start Refutation
% 3.94/4.15  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.94/4.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.94/4.15  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.94/4.15  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.94/4.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.94/4.15  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.94/4.15  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.94/4.15  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.94/4.15  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.94/4.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.94/4.15  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.94/4.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.94/4.15  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.94/4.15  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.94/4.15  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.94/4.15  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.94/4.15  thf(sk_A_type, type, sk_A: $i).
% 3.94/4.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.94/4.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.94/4.15  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.94/4.15  thf(sk_D_type, type, sk_D: $i).
% 3.94/4.15  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.94/4.15  thf(sk_C_type, type, sk_C: $i).
% 3.94/4.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.94/4.15  thf(sk_B_type, type, sk_B: $i).
% 3.94/4.15  thf(t29_funct_2, conjecture,
% 3.94/4.15    (![A:$i,B:$i,C:$i]:
% 3.94/4.15     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.94/4.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.94/4.15       ( ![D:$i]:
% 3.94/4.15         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.94/4.15             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.94/4.15           ( ( r2_relset_1 @
% 3.94/4.15               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.94/4.15               ( k6_partfun1 @ A ) ) =>
% 3.94/4.15             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.94/4.15  thf(zf_stmt_0, negated_conjecture,
% 3.94/4.15    (~( ![A:$i,B:$i,C:$i]:
% 3.94/4.15        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.94/4.15            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.94/4.15          ( ![D:$i]:
% 3.94/4.15            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.94/4.15                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.94/4.15              ( ( r2_relset_1 @
% 3.94/4.15                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.94/4.15                  ( k6_partfun1 @ A ) ) =>
% 3.94/4.15                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.94/4.15    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.94/4.15  thf('0', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('1', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf(redefinition_k1_partfun1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.94/4.15     ( ( ( v1_funct_1 @ E ) & 
% 3.94/4.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.94/4.15         ( v1_funct_1 @ F ) & 
% 3.94/4.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.94/4.15       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.94/4.15  thf('2', plain,
% 3.94/4.15      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.94/4.15         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.94/4.15          | ~ (v1_funct_1 @ X39)
% 3.94/4.15          | ~ (v1_funct_1 @ X42)
% 3.94/4.15          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.94/4.15          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 3.94/4.15              = (k5_relat_1 @ X39 @ X42)))),
% 3.94/4.15      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.94/4.15  thf('3', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.94/4.15            = (k5_relat_1 @ sk_C @ X0))
% 3.94/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.94/4.15          | ~ (v1_funct_1 @ X0)
% 3.94/4.15          | ~ (v1_funct_1 @ sk_C))),
% 3.94/4.15      inference('sup-', [status(thm)], ['1', '2'])).
% 3.94/4.15  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('5', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.94/4.15            = (k5_relat_1 @ sk_C @ X0))
% 3.94/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.94/4.15          | ~ (v1_funct_1 @ X0))),
% 3.94/4.15      inference('demod', [status(thm)], ['3', '4'])).
% 3.94/4.15  thf('6', plain,
% 3.94/4.15      ((~ (v1_funct_1 @ sk_C)
% 3.94/4.15        | ((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 3.94/4.15            = (k5_relat_1 @ sk_C @ sk_C)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['0', '5'])).
% 3.94/4.15  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('8', plain,
% 3.94/4.15      (((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 3.94/4.15         = (k5_relat_1 @ sk_C @ sk_C))),
% 3.94/4.15      inference('demod', [status(thm)], ['6', '7'])).
% 3.94/4.15  thf(l13_xboole_0, axiom,
% 3.94/4.15    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.94/4.15  thf('9', plain,
% 3.94/4.15      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.94/4.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.94/4.15  thf(fc4_zfmisc_1, axiom,
% 3.94/4.15    (![A:$i,B:$i]:
% 3.94/4.15     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 3.94/4.15  thf('10', plain,
% 3.94/4.15      (![X8 : $i, X9 : $i]:
% 3.94/4.15         (~ (v1_xboole_0 @ X8) | (v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 3.94/4.15      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 3.94/4.15  thf('11', plain,
% 3.94/4.15      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.94/4.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.94/4.15  thf('12', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['10', '11'])).
% 3.94/4.15  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.94/4.15  thf('13', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.94/4.15      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.94/4.15  thf(redefinition_k6_partfun1, axiom,
% 3.94/4.15    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.94/4.15  thf('14', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 3.94/4.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.94/4.15  thf('15', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.94/4.15      inference('demod', [status(thm)], ['13', '14'])).
% 3.94/4.15  thf(t29_relset_1, axiom,
% 3.94/4.15    (![A:$i]:
% 3.94/4.15     ( m1_subset_1 @
% 3.94/4.15       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.94/4.15  thf('16', plain,
% 3.94/4.15      (![X30 : $i]:
% 3.94/4.15         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 3.94/4.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 3.94/4.15      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.94/4.15  thf('17', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 3.94/4.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.94/4.15  thf('18', plain,
% 3.94/4.15      (![X30 : $i]:
% 3.94/4.15         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 3.94/4.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 3.94/4.15      inference('demod', [status(thm)], ['16', '17'])).
% 3.94/4.15  thf('19', plain,
% 3.94/4.15      ((m1_subset_1 @ k1_xboole_0 @ 
% 3.94/4.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['15', '18'])).
% 3.94/4.15  thf('20', plain,
% 3.94/4.15      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.94/4.15        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['12', '19'])).
% 3.94/4.15  thf(d10_xboole_0, axiom,
% 3.94/4.15    (![A:$i,B:$i]:
% 3.94/4.15     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.94/4.15  thf('21', plain,
% 3.94/4.15      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 3.94/4.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.94/4.15  thf('22', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 3.94/4.15      inference('simplify', [status(thm)], ['21'])).
% 3.94/4.15  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 3.94/4.15  thf('23', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 3.94/4.15      inference('cnf', [status(esa)], [t65_xboole_1])).
% 3.94/4.15  thf(t69_xboole_1, axiom,
% 3.94/4.15    (![A:$i,B:$i]:
% 3.94/4.15     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.94/4.15       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 3.94/4.15  thf('24', plain,
% 3.94/4.15      (![X6 : $i, X7 : $i]:
% 3.94/4.15         (~ (r1_xboole_0 @ X6 @ X7)
% 3.94/4.15          | ~ (r1_tarski @ X6 @ X7)
% 3.94/4.15          | (v1_xboole_0 @ X6))),
% 3.94/4.15      inference('cnf', [status(esa)], [t69_xboole_1])).
% 3.94/4.15  thf('25', plain,
% 3.94/4.15      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 3.94/4.15      inference('sup-', [status(thm)], ['23', '24'])).
% 3.94/4.15  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.94/4.15      inference('sup-', [status(thm)], ['22', '25'])).
% 3.94/4.15  thf('27', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.94/4.15      inference('demod', [status(thm)], ['20', '26'])).
% 3.94/4.15  thf('28', plain,
% 3.94/4.15      (![X0 : $i]:
% 3.94/4.15         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.94/4.15          | ~ (v1_xboole_0 @ X0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['9', '27'])).
% 3.94/4.15  thf('29', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['10', '11'])).
% 3.94/4.15  thf('30', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf(dt_k1_partfun1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.94/4.15     ( ( ( v1_funct_1 @ E ) & 
% 3.94/4.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.94/4.15         ( v1_funct_1 @ F ) & 
% 3.94/4.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.94/4.15       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.94/4.15         ( m1_subset_1 @
% 3.94/4.15           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.94/4.15           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.94/4.15  thf('31', plain,
% 3.94/4.15      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.94/4.15         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.94/4.15          | ~ (v1_funct_1 @ X33)
% 3.94/4.15          | ~ (v1_funct_1 @ X36)
% 3.94/4.15          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.94/4.15          | (v1_funct_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)))),
% 3.94/4.15      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.94/4.15  thf('32', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 3.94/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.94/4.15          | ~ (v1_funct_1 @ X0)
% 3.94/4.15          | ~ (v1_funct_1 @ sk_C))),
% 3.94/4.15      inference('sup-', [status(thm)], ['30', '31'])).
% 3.94/4.15  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('34', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 3.94/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.94/4.15          | ~ (v1_funct_1 @ X0))),
% 3.94/4.15      inference('demod', [status(thm)], ['32', '33'])).
% 3.94/4.15  thf('35', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.94/4.15          | ~ (v1_xboole_0 @ X1)
% 3.94/4.15          | ~ (v1_funct_1 @ X2)
% 3.94/4.15          | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X1 @ X0 @ sk_C @ X2)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['29', '34'])).
% 3.94/4.15  thf('36', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         (~ (v1_xboole_0 @ X0)
% 3.94/4.15          | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 3.94/4.15          | ~ (v1_funct_1 @ X0)
% 3.94/4.15          | ~ (v1_xboole_0 @ X2))),
% 3.94/4.15      inference('sup-', [status(thm)], ['28', '35'])).
% 3.94/4.15  thf('37', plain,
% 3.94/4.15      (((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))
% 3.94/4.15        | ~ (v1_xboole_0 @ sk_A)
% 3.94/4.15        | ~ (v1_funct_1 @ sk_C)
% 3.94/4.15        | ~ (v1_xboole_0 @ sk_C))),
% 3.94/4.15      inference('sup+', [status(thm)], ['8', '36'])).
% 3.94/4.15  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('39', plain,
% 3.94/4.15      (((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))
% 3.94/4.15        | ~ (v1_xboole_0 @ sk_A)
% 3.94/4.15        | ~ (v1_xboole_0 @ sk_C))),
% 3.94/4.15      inference('demod', [status(thm)], ['37', '38'])).
% 3.94/4.15  thf('40', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('41', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 3.94/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.94/4.15          | ~ (v1_funct_1 @ X0))),
% 3.94/4.15      inference('demod', [status(thm)], ['32', '33'])).
% 3.94/4.15  thf('42', plain,
% 3.94/4.15      ((~ (v1_funct_1 @ sk_C)
% 3.94/4.15        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['40', '41'])).
% 3.94/4.15  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('44', plain,
% 3.94/4.15      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C))),
% 3.94/4.15      inference('demod', [status(thm)], ['42', '43'])).
% 3.94/4.15  thf('45', plain,
% 3.94/4.15      (((k1_partfun1 @ sk_A @ sk_B @ sk_A @ sk_B @ sk_C @ sk_C)
% 3.94/4.15         = (k5_relat_1 @ sk_C @ sk_C))),
% 3.94/4.15      inference('demod', [status(thm)], ['6', '7'])).
% 3.94/4.15  thf('46', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_C))),
% 3.94/4.15      inference('demod', [status(thm)], ['44', '45'])).
% 3.94/4.15  thf('47', plain, (($true | ~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C))),
% 3.94/4.15      inference('demod', [status(thm)], ['39', '46'])).
% 3.94/4.15  thf('48', plain,
% 3.94/4.15      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.94/4.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.94/4.15  thf('49', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.94/4.15      inference('demod', [status(thm)], ['13', '14'])).
% 3.94/4.15  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.94/4.15  thf('50', plain, (![X22 : $i]: (v2_funct_1 @ (k6_relat_1 @ X22))),
% 3.94/4.15      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.94/4.15  thf('51', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 3.94/4.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.94/4.15  thf('52', plain, (![X22 : $i]: (v2_funct_1 @ (k6_partfun1 @ X22))),
% 3.94/4.15      inference('demod', [status(thm)], ['50', '51'])).
% 3.94/4.15  thf('53', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.94/4.15      inference('sup+', [status(thm)], ['49', '52'])).
% 3.94/4.15  thf('54', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['48', '53'])).
% 3.94/4.15  thf('55', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('56', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.94/4.15      inference('split', [status(esa)], ['55'])).
% 3.94/4.15  thf('57', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['54', '56'])).
% 3.94/4.15  thf('58', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('59', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.94/4.15            = (k5_relat_1 @ sk_C @ X0))
% 3.94/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.94/4.15          | ~ (v1_funct_1 @ X0))),
% 3.94/4.15      inference('demod', [status(thm)], ['3', '4'])).
% 3.94/4.15  thf('60', plain,
% 3.94/4.15      ((~ (v1_funct_1 @ sk_D)
% 3.94/4.15        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.94/4.15            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['58', '59'])).
% 3.94/4.15  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('62', plain,
% 3.94/4.15      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.94/4.15        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.94/4.15        (k6_partfun1 @ sk_A))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('63', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('64', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('65', plain,
% 3.94/4.15      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.94/4.15         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.94/4.15          | ~ (v1_funct_1 @ X33)
% 3.94/4.15          | ~ (v1_funct_1 @ X36)
% 3.94/4.15          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.94/4.15          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 3.94/4.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 3.94/4.15      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.94/4.15  thf('66', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.94/4.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.94/4.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.94/4.15          | ~ (v1_funct_1 @ X1)
% 3.94/4.15          | ~ (v1_funct_1 @ sk_C))),
% 3.94/4.15      inference('sup-', [status(thm)], ['64', '65'])).
% 3.94/4.15  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('68', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.94/4.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.94/4.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.94/4.15          | ~ (v1_funct_1 @ X1))),
% 3.94/4.15      inference('demod', [status(thm)], ['66', '67'])).
% 3.94/4.15  thf('69', plain,
% 3.94/4.15      ((~ (v1_funct_1 @ sk_D)
% 3.94/4.15        | (m1_subset_1 @ 
% 3.94/4.15           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.94/4.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.94/4.15      inference('sup-', [status(thm)], ['63', '68'])).
% 3.94/4.15  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('71', plain,
% 3.94/4.15      ((m1_subset_1 @ 
% 3.94/4.15        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.94/4.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.94/4.15      inference('demod', [status(thm)], ['69', '70'])).
% 3.94/4.15  thf(redefinition_r2_relset_1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i,D:$i]:
% 3.94/4.15     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.94/4.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.94/4.15       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.94/4.15  thf('72', plain,
% 3.94/4.15      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.94/4.15         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.94/4.15          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.94/4.15          | ((X26) = (X29))
% 3.94/4.15          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 3.94/4.15      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.94/4.15  thf('73', plain,
% 3.94/4.15      (![X0 : $i]:
% 3.94/4.15         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.94/4.15             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.94/4.15          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.94/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.94/4.15      inference('sup-', [status(thm)], ['71', '72'])).
% 3.94/4.15  thf('74', plain,
% 3.94/4.15      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.94/4.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.94/4.15        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.94/4.15            = (k6_partfun1 @ sk_A)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['62', '73'])).
% 3.94/4.15  thf('75', plain,
% 3.94/4.15      (![X30 : $i]:
% 3.94/4.15         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 3.94/4.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 3.94/4.15      inference('demod', [status(thm)], ['16', '17'])).
% 3.94/4.15  thf('76', plain,
% 3.94/4.15      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.94/4.15         = (k6_partfun1 @ sk_A))),
% 3.94/4.15      inference('demod', [status(thm)], ['74', '75'])).
% 3.94/4.15  thf('77', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.94/4.15      inference('demod', [status(thm)], ['60', '61', '76'])).
% 3.94/4.15  thf(t45_relat_1, axiom,
% 3.94/4.15    (![A:$i]:
% 3.94/4.15     ( ( v1_relat_1 @ A ) =>
% 3.94/4.15       ( ![B:$i]:
% 3.94/4.15         ( ( v1_relat_1 @ B ) =>
% 3.94/4.15           ( r1_tarski @
% 3.94/4.15             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.94/4.15  thf('78', plain,
% 3.94/4.15      (![X18 : $i, X19 : $i]:
% 3.94/4.15         (~ (v1_relat_1 @ X18)
% 3.94/4.15          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X19 @ X18)) @ 
% 3.94/4.15             (k2_relat_1 @ X18))
% 3.94/4.15          | ~ (v1_relat_1 @ X19))),
% 3.94/4.15      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.94/4.15  thf('79', plain,
% 3.94/4.15      (![X1 : $i, X3 : $i]:
% 3.94/4.15         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 3.94/4.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.94/4.15  thf('80', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         (~ (v1_relat_1 @ X1)
% 3.94/4.15          | ~ (v1_relat_1 @ X0)
% 3.94/4.15          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 3.94/4.15               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.94/4.15          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 3.94/4.15      inference('sup-', [status(thm)], ['78', '79'])).
% 3.94/4.15  thf('81', plain,
% 3.94/4.15      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 3.94/4.15           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 3.94/4.15        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 3.94/4.15        | ~ (v1_relat_1 @ sk_D)
% 3.94/4.15        | ~ (v1_relat_1 @ sk_C))),
% 3.94/4.15      inference('sup-', [status(thm)], ['77', '80'])).
% 3.94/4.15  thf(t71_relat_1, axiom,
% 3.94/4.15    (![A:$i]:
% 3.94/4.15     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.94/4.15       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.94/4.15  thf('82', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 3.94/4.15      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.94/4.15  thf('83', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 3.94/4.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.94/4.15  thf('84', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 3.94/4.15      inference('demod', [status(thm)], ['82', '83'])).
% 3.94/4.15  thf('85', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf(cc2_relset_1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i]:
% 3.94/4.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.94/4.15       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.94/4.15  thf('86', plain,
% 3.94/4.15      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.94/4.15         ((v5_relat_1 @ X23 @ X25)
% 3.94/4.15          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.94/4.15      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.94/4.15  thf('87', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.94/4.15      inference('sup-', [status(thm)], ['85', '86'])).
% 3.94/4.15  thf(d19_relat_1, axiom,
% 3.94/4.15    (![A:$i,B:$i]:
% 3.94/4.15     ( ( v1_relat_1 @ B ) =>
% 3.94/4.15       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.94/4.15  thf('88', plain,
% 3.94/4.15      (![X14 : $i, X15 : $i]:
% 3.94/4.15         (~ (v5_relat_1 @ X14 @ X15)
% 3.94/4.15          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 3.94/4.15          | ~ (v1_relat_1 @ X14))),
% 3.94/4.15      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.94/4.15  thf('89', plain,
% 3.94/4.15      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 3.94/4.15      inference('sup-', [status(thm)], ['87', '88'])).
% 3.94/4.15  thf('90', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf(cc2_relat_1, axiom,
% 3.94/4.15    (![A:$i]:
% 3.94/4.15     ( ( v1_relat_1 @ A ) =>
% 3.94/4.15       ( ![B:$i]:
% 3.94/4.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.94/4.15  thf('91', plain,
% 3.94/4.15      (![X12 : $i, X13 : $i]:
% 3.94/4.15         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 3.94/4.15          | (v1_relat_1 @ X12)
% 3.94/4.15          | ~ (v1_relat_1 @ X13))),
% 3.94/4.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.94/4.15  thf('92', plain,
% 3.94/4.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.94/4.15      inference('sup-', [status(thm)], ['90', '91'])).
% 3.94/4.15  thf(fc6_relat_1, axiom,
% 3.94/4.15    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.94/4.15  thf('93', plain,
% 3.94/4.15      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 3.94/4.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.94/4.15  thf('94', plain, ((v1_relat_1 @ sk_D)),
% 3.94/4.15      inference('demod', [status(thm)], ['92', '93'])).
% 3.94/4.15  thf('95', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 3.94/4.15      inference('demod', [status(thm)], ['89', '94'])).
% 3.94/4.15  thf('96', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.94/4.15      inference('demod', [status(thm)], ['60', '61', '76'])).
% 3.94/4.15  thf('97', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 3.94/4.15      inference('demod', [status(thm)], ['82', '83'])).
% 3.94/4.15  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 3.94/4.15      inference('demod', [status(thm)], ['92', '93'])).
% 3.94/4.15  thf('99', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('100', plain,
% 3.94/4.15      (![X12 : $i, X13 : $i]:
% 3.94/4.15         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 3.94/4.15          | (v1_relat_1 @ X12)
% 3.94/4.15          | ~ (v1_relat_1 @ X13))),
% 3.94/4.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.94/4.15  thf('101', plain,
% 3.94/4.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.94/4.15      inference('sup-', [status(thm)], ['99', '100'])).
% 3.94/4.15  thf('102', plain,
% 3.94/4.15      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 3.94/4.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.94/4.15  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 3.94/4.15      inference('demod', [status(thm)], ['101', '102'])).
% 3.94/4.15  thf('104', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.94/4.15      inference('demod', [status(thm)],
% 3.94/4.15                ['81', '84', '95', '96', '97', '98', '103'])).
% 3.94/4.15  thf('105', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 3.94/4.15      inference('simplify', [status(thm)], ['21'])).
% 3.94/4.15  thf('106', plain,
% 3.94/4.15      (![X14 : $i, X15 : $i]:
% 3.94/4.15         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 3.94/4.15          | (v5_relat_1 @ X14 @ X15)
% 3.94/4.15          | ~ (v1_relat_1 @ X14))),
% 3.94/4.15      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.94/4.15  thf('107', plain,
% 3.94/4.15      (![X0 : $i]:
% 3.94/4.15         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['105', '106'])).
% 3.94/4.15  thf(d3_funct_2, axiom,
% 3.94/4.15    (![A:$i,B:$i]:
% 3.94/4.15     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.94/4.15       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.94/4.15  thf('108', plain,
% 3.94/4.15      (![X31 : $i, X32 : $i]:
% 3.94/4.15         (((k2_relat_1 @ X32) != (X31))
% 3.94/4.15          | (v2_funct_2 @ X32 @ X31)
% 3.94/4.15          | ~ (v5_relat_1 @ X32 @ X31)
% 3.94/4.15          | ~ (v1_relat_1 @ X32))),
% 3.94/4.15      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.94/4.15  thf('109', plain,
% 3.94/4.15      (![X32 : $i]:
% 3.94/4.15         (~ (v1_relat_1 @ X32)
% 3.94/4.15          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 3.94/4.15          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 3.94/4.15      inference('simplify', [status(thm)], ['108'])).
% 3.94/4.15  thf('110', plain,
% 3.94/4.15      (![X0 : $i]:
% 3.94/4.15         (~ (v1_relat_1 @ X0)
% 3.94/4.15          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.94/4.15          | ~ (v1_relat_1 @ X0))),
% 3.94/4.15      inference('sup-', [status(thm)], ['107', '109'])).
% 3.94/4.15  thf('111', plain,
% 3.94/4.15      (![X0 : $i]:
% 3.94/4.15         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.94/4.15      inference('simplify', [status(thm)], ['110'])).
% 3.94/4.15  thf('112', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.94/4.15      inference('sup+', [status(thm)], ['104', '111'])).
% 3.94/4.15  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 3.94/4.15      inference('demod', [status(thm)], ['92', '93'])).
% 3.94/4.15  thf('114', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.94/4.15      inference('demod', [status(thm)], ['112', '113'])).
% 3.94/4.15  thf('115', plain,
% 3.94/4.15      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.94/4.15      inference('split', [status(esa)], ['55'])).
% 3.94/4.15  thf('116', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.94/4.15      inference('sup-', [status(thm)], ['114', '115'])).
% 3.94/4.15  thf('117', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.94/4.15      inference('split', [status(esa)], ['55'])).
% 3.94/4.15  thf('118', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.94/4.15      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 3.94/4.15  thf('119', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.94/4.15      inference('simpl_trail', [status(thm)], ['57', '118'])).
% 3.94/4.15  thf('120', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.94/4.15      inference('clc', [status(thm)], ['47', '119'])).
% 3.94/4.15  thf('121', plain,
% 3.94/4.15      (![X8 : $i, X9 : $i]:
% 3.94/4.15         (~ (v1_xboole_0 @ X8) | (v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 3.94/4.15      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 3.94/4.15  thf('122', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf(cc1_subset_1, axiom,
% 3.94/4.15    (![A:$i]:
% 3.94/4.15     ( ( v1_xboole_0 @ A ) =>
% 3.94/4.15       ( ![B:$i]:
% 3.94/4.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.94/4.15  thf('123', plain,
% 3.94/4.15      (![X10 : $i, X11 : $i]:
% 3.94/4.15         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 3.94/4.15          | (v1_xboole_0 @ X10)
% 3.94/4.15          | ~ (v1_xboole_0 @ X11))),
% 3.94/4.15      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.94/4.15  thf('124', plain,
% 3.94/4.15      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.94/4.15      inference('sup-', [status(thm)], ['122', '123'])).
% 3.94/4.15  thf('125', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 3.94/4.15      inference('sup-', [status(thm)], ['121', '124'])).
% 3.94/4.15  thf('126', plain, (~ (v1_xboole_0 @ sk_A)),
% 3.94/4.15      inference('clc', [status(thm)], ['120', '125'])).
% 3.94/4.15  thf('127', plain,
% 3.94/4.15      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.94/4.15         = (k6_partfun1 @ sk_A))),
% 3.94/4.15      inference('demod', [status(thm)], ['74', '75'])).
% 3.94/4.15  thf('128', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf(t26_funct_2, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i,D:$i]:
% 3.94/4.15     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.94/4.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.94/4.15       ( ![E:$i]:
% 3.94/4.15         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.94/4.15             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.94/4.15           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.94/4.15             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.94/4.15               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.94/4.15  thf('129', plain,
% 3.94/4.15      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 3.94/4.15         (~ (v1_funct_1 @ X46)
% 3.94/4.15          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 3.94/4.15          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 3.94/4.15          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X47 @ X47 @ X48 @ X50 @ X46))
% 3.94/4.15          | (v2_funct_1 @ X50)
% 3.94/4.15          | ((X48) = (k1_xboole_0))
% 3.94/4.15          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 3.94/4.15          | ~ (v1_funct_2 @ X50 @ X49 @ X47)
% 3.94/4.15          | ~ (v1_funct_1 @ X50))),
% 3.94/4.15      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.94/4.15  thf('130', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         (~ (v1_funct_1 @ X0)
% 3.94/4.15          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.94/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.94/4.15          | ((sk_A) = (k1_xboole_0))
% 3.94/4.15          | (v2_funct_1 @ X0)
% 3.94/4.15          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.94/4.15          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.94/4.15          | ~ (v1_funct_1 @ sk_D))),
% 3.94/4.15      inference('sup-', [status(thm)], ['128', '129'])).
% 3.94/4.15  thf('131', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('132', plain, ((v1_funct_1 @ sk_D)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('133', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         (~ (v1_funct_1 @ X0)
% 3.94/4.15          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.94/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.94/4.15          | ((sk_A) = (k1_xboole_0))
% 3.94/4.15          | (v2_funct_1 @ X0)
% 3.94/4.15          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.94/4.15      inference('demod', [status(thm)], ['130', '131', '132'])).
% 3.94/4.15  thf('134', plain,
% 3.94/4.15      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.94/4.15        | (v2_funct_1 @ sk_C)
% 3.94/4.15        | ((sk_A) = (k1_xboole_0))
% 3.94/4.15        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.94/4.15        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.94/4.15        | ~ (v1_funct_1 @ sk_C))),
% 3.94/4.15      inference('sup-', [status(thm)], ['127', '133'])).
% 3.94/4.15  thf('135', plain, (![X22 : $i]: (v2_funct_1 @ (k6_partfun1 @ X22))),
% 3.94/4.15      inference('demod', [status(thm)], ['50', '51'])).
% 3.94/4.15  thf('136', plain,
% 3.94/4.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('137', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('139', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.94/4.15      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 3.94/4.15  thf('140', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.94/4.15      inference('split', [status(esa)], ['55'])).
% 3.94/4.15  thf('141', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.94/4.15      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 3.94/4.15  thf('142', plain, (~ (v2_funct_1 @ sk_C)),
% 3.94/4.15      inference('simpl_trail', [status(thm)], ['140', '141'])).
% 3.94/4.15  thf('143', plain, (((sk_A) = (k1_xboole_0))),
% 3.94/4.15      inference('clc', [status(thm)], ['139', '142'])).
% 3.94/4.15  thf('144', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.94/4.15      inference('sup-', [status(thm)], ['22', '25'])).
% 3.94/4.15  thf('145', plain, ($false),
% 3.94/4.15      inference('demod', [status(thm)], ['126', '143', '144'])).
% 3.94/4.15  
% 3.94/4.15  % SZS output end Refutation
% 3.94/4.15  
% 3.94/4.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
