%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIeEJlBGvE

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:31 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  187 (4287 expanded)
%              Number of leaves         :   36 (1321 expanded)
%              Depth                    :   43
%              Number of atoms          : 1345 (67900 expanded)
%              Number of equality atoms :   55 (2066 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k1_relat_1 @ X26 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('11',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('12',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('40',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['20','21'])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('48',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48','49'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X47: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('55',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('63',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf(t9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('66',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ X53 @ X54 )
      | ( zip_tseitin_1 @ X53 @ X55 )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_funct_2 @ X56 @ X55 @ X53 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X53 ) ) )
      | ( zip_tseitin_0 @ X56 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k1_relat_1 @ X26 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('69',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('70',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('71',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48','49'])).

thf('72',plain,(
    ! [X47: $i] :
      ( ( v1_funct_2 @ X47 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('73',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('76',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['68','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('84',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['67','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','91'])).

thf('93',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( zip_tseitin_0 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('94',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('98',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['95'])).

thf('100',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','91'])).

thf('105',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( zip_tseitin_0 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('106',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['95'])).

thf('108',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('110',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('111',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('114',plain,(
    ! [X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X24 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('115',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['20','21'])).

thf('118',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['112','119'])).

thf('121',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('122',plain,(
    ! [X51: $i] :
      ~ ( zip_tseitin_1 @ X51 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['120','122'])).

thf('124',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['95'])).

thf('125',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['103','123','124'])).

thf('126',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['96','125'])).

thf('127',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['94','126'])).

thf('128',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['94','126'])).

thf('129',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('130',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    zip_tseitin_1 @ k1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['127','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('133',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('134',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k1_relat_1 @ X26 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('136',plain,(
    ! [X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X24 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48','49'])).

thf('140',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('143',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['128','129'])).

thf('145',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['131','146'])).

thf('148',plain,(
    ! [X51: $i] :
      ~ ( zip_tseitin_1 @ X51 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('149',plain,(
    $false ),
    inference('sup-',[status(thm)],['147','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIeEJlBGvE
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:41:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 1030 iterations in 0.326s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.79  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.59/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.79  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.59/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.59/0.79  thf(t31_funct_2, conjecture,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.79       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.59/0.79         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.59/0.79           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.59/0.79           ( m1_subset_1 @
% 0.59/0.79             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.79        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.79            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.79          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.59/0.79            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.59/0.79              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.59/0.79              ( m1_subset_1 @
% 0.59/0.79                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(cc2_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.59/0.79         ((v4_relat_1 @ X30 @ X31)
% 0.59/0.79          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.79  thf('2', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.79  thf(d18_relat_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ B ) =>
% 0.59/0.79       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X17 : $i, X18 : $i]:
% 0.59/0.79         (~ (v4_relat_1 @ X17 @ X18)
% 0.59/0.79          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.59/0.79          | ~ (v1_relat_1 @ X17))),
% 0.59/0.79      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(cc1_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( v1_relat_1 @ C ) ))).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.79         ((v1_relat_1 @ X27)
% 0.59/0.79          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.79  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('8', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '7'])).
% 0.59/0.79  thf(dt_k2_funct_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.79       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.59/0.79         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X25 : $i]:
% 0.59/0.79         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 0.59/0.79          | ~ (v1_funct_1 @ X25)
% 0.59/0.79          | ~ (v1_relat_1 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.59/0.79  thf(t55_funct_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.79       ( ( v2_funct_1 @ A ) =>
% 0.59/0.79         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.59/0.79           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X26 : $i]:
% 0.59/0.79         (~ (v2_funct_1 @ X26)
% 0.59/0.79          | ((k1_relat_1 @ X26) = (k2_relat_1 @ (k2_funct_1 @ X26)))
% 0.59/0.79          | ~ (v1_funct_1 @ X26)
% 0.59/0.79          | ~ (v1_relat_1 @ X26))),
% 0.59/0.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X25 : $i]:
% 0.59/0.79         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 0.59/0.79          | ~ (v1_funct_1 @ X25)
% 0.59/0.79          | ~ (v1_relat_1 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X25 : $i]:
% 0.59/0.79         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 0.59/0.79          | ~ (v1_funct_1 @ X25)
% 0.59/0.79          | ~ (v1_relat_1 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X26 : $i]:
% 0.59/0.79         (~ (v2_funct_1 @ X26)
% 0.59/0.79          | ((k2_relat_1 @ X26) = (k1_relat_1 @ (k2_funct_1 @ X26)))
% 0.59/0.79          | ~ (v1_funct_1 @ X26)
% 0.59/0.79          | ~ (v1_relat_1 @ X26))),
% 0.59/0.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (![X25 : $i]:
% 0.59/0.79         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 0.59/0.79          | ~ (v1_funct_1 @ X25)
% 0.59/0.79          | ~ (v1_relat_1 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.59/0.79  thf(d10_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.79      inference('simplify', [status(thm)], ['15'])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X25 : $i]:
% 0.59/0.79         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 0.59/0.79          | ~ (v1_funct_1 @ X25)
% 0.59/0.79          | ~ (v1_relat_1 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(redefinition_k2_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.59/0.79         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.59/0.79          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.59/0.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['18', '19'])).
% 0.59/0.79  thf('21', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('22', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (![X26 : $i]:
% 0.59/0.79         (~ (v2_funct_1 @ X26)
% 0.59/0.79          | ((k2_relat_1 @ X26) = (k1_relat_1 @ (k2_funct_1 @ X26)))
% 0.59/0.79          | ~ (v1_funct_1 @ X26)
% 0.59/0.79          | ~ (v1_relat_1 @ X26))),
% 0.59/0.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (![X17 : $i, X18 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.59/0.79          | (v4_relat_1 @ X17 @ X18)
% 0.59/0.79          | ~ (v1_relat_1 @ X17))),
% 0.59/0.79      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_funct_1 @ X0)
% 0.59/0.79          | ~ (v2_funct_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.79          | (v4_relat_1 @ (k2_funct_1 @ X0) @ X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ sk_B @ X0)
% 0.59/0.79          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79          | ~ (v2_funct_1 @ sk_C_1)
% 0.59/0.79          | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79          | ~ (v1_relat_1 @ sk_C_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['22', '25'])).
% 0.59/0.79  thf('27', plain, ((v2_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ sk_B @ X0)
% 0.59/0.79          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79          | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 0.59/0.79          | ~ (r1_tarski @ sk_B @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['17', '30'])).
% 0.59/0.79  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('33', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('34', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.59/0.79  thf('35', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B)),
% 0.59/0.79      inference('sup-', [status(thm)], ['16', '34'])).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      (![X17 : $i, X18 : $i]:
% 0.59/0.79         (~ (v4_relat_1 @ X17 @ X18)
% 0.59/0.79          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.59/0.79          | ~ (v1_relat_1 @ X17))),
% 0.59/0.79      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.59/0.79  thf('37', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.79  thf('38', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['14', '37'])).
% 0.59/0.79  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('40', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('41', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B)),
% 0.59/0.79      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.59/0.79  thf('42', plain,
% 0.59/0.79      (![X0 : $i, X2 : $i]:
% 0.59/0.79         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.59/0.79        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.79  thf('44', plain,
% 0.59/0.79      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79        | ~ (v2_funct_1 @ sk_C_1)
% 0.59/0.79        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['13', '43'])).
% 0.59/0.79  thf('45', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.79      inference('simplify', [status(thm)], ['15'])).
% 0.59/0.79  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('49', plain, ((v2_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('50', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['44', '45', '46', '47', '48', '49'])).
% 0.59/0.79  thf(t3_funct_2, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.79       ( ( v1_funct_1 @ A ) & 
% 0.59/0.79         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.59/0.79         ( m1_subset_1 @
% 0.59/0.79           A @ 
% 0.59/0.79           ( k1_zfmisc_1 @
% 0.59/0.79             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.79  thf('51', plain,
% 0.59/0.79      (![X47 : $i]:
% 0.59/0.79         ((m1_subset_1 @ X47 @ 
% 0.59/0.79           (k1_zfmisc_1 @ 
% 0.59/0.79            (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))))
% 0.59/0.79          | ~ (v1_funct_1 @ X47)
% 0.59/0.79          | ~ (v1_relat_1 @ X47))),
% 0.59/0.79      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79         (k1_zfmisc_1 @ 
% 0.59/0.79          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 0.59/0.79        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['50', '51'])).
% 0.59/0.79  thf('53', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79           (k1_zfmisc_1 @ 
% 0.59/0.79            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['12', '52'])).
% 0.59/0.79  thf('54', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('55', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('56', plain,
% 0.59/0.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79           (k1_zfmisc_1 @ 
% 0.59/0.79            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 0.59/0.79      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.59/0.79  thf('57', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79           (k1_zfmisc_1 @ 
% 0.59/0.79            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['11', '56'])).
% 0.59/0.79  thf('58', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('60', plain,
% 0.59/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 0.59/0.79      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.59/0.79  thf('61', plain,
% 0.59/0.79      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79        | ~ (v2_funct_1 @ sk_C_1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['10', '60'])).
% 0.59/0.79  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('63', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('64', plain, ((v2_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('65', plain,
% 0.59/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.59/0.79      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.59/0.79  thf(t9_funct_2, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.79         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.59/0.79       ( ( r1_tarski @ B @ C ) =>
% 0.59/0.79         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.59/0.79             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.59/0.79           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.59/0.79  thf(zf_stmt_2, axiom,
% 0.59/0.79    (![B:$i,A:$i]:
% 0.59/0.79     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.59/0.79       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.59/0.79  thf(zf_stmt_4, axiom,
% 0.59/0.79    (![D:$i,C:$i,A:$i]:
% 0.59/0.79     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.59/0.79       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.59/0.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_5, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.59/0.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.79       ( ( r1_tarski @ B @ C ) =>
% 0.59/0.79         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.59/0.79  thf('66', plain,
% 0.59/0.79      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.59/0.79         (~ (r1_tarski @ X53 @ X54)
% 0.59/0.79          | (zip_tseitin_1 @ X53 @ X55)
% 0.59/0.79          | ~ (v1_funct_1 @ X56)
% 0.59/0.79          | ~ (v1_funct_2 @ X56 @ X55 @ X53)
% 0.59/0.79          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X53)))
% 0.59/0.79          | (zip_tseitin_0 @ X56 @ X54 @ X55))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.79  thf('67', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 0.59/0.79          | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.59/0.79               (k1_relat_1 @ sk_C_1))
% 0.59/0.79          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.59/0.79          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.79  thf('68', plain,
% 0.59/0.79      (![X26 : $i]:
% 0.59/0.79         (~ (v2_funct_1 @ X26)
% 0.59/0.79          | ((k1_relat_1 @ X26) = (k2_relat_1 @ (k2_funct_1 @ X26)))
% 0.59/0.79          | ~ (v1_funct_1 @ X26)
% 0.59/0.79          | ~ (v1_relat_1 @ X26))),
% 0.59/0.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.79  thf('69', plain,
% 0.59/0.79      (![X25 : $i]:
% 0.59/0.79         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 0.59/0.79          | ~ (v1_funct_1 @ X25)
% 0.59/0.79          | ~ (v1_relat_1 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.59/0.79  thf('70', plain,
% 0.59/0.79      (![X25 : $i]:
% 0.59/0.79         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 0.59/0.79          | ~ (v1_funct_1 @ X25)
% 0.59/0.79          | ~ (v1_relat_1 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.59/0.79  thf('71', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['44', '45', '46', '47', '48', '49'])).
% 0.59/0.79  thf('72', plain,
% 0.59/0.79      (![X47 : $i]:
% 0.59/0.79         ((v1_funct_2 @ X47 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))
% 0.59/0.79          | ~ (v1_funct_1 @ X47)
% 0.59/0.79          | ~ (v1_relat_1 @ X47))),
% 0.59/0.79      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.59/0.79  thf('73', plain,
% 0.59/0.79      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.59/0.79         (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.59/0.79        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['71', '72'])).
% 0.59/0.79  thf('74', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.59/0.79           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['70', '73'])).
% 0.59/0.79  thf('75', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('76', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('77', plain,
% 0.59/0.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.59/0.79           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.59/0.79      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.59/0.79  thf('78', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.59/0.79           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['69', '77'])).
% 0.59/0.79  thf('79', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('81', plain,
% 0.59/0.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.59/0.79        (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.59/0.79  thf('82', plain,
% 0.59/0.79      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79        | ~ (v2_funct_1 @ sk_C_1))),
% 0.59/0.79      inference('sup+', [status(thm)], ['68', '81'])).
% 0.59/0.79  thf('83', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('84', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('85', plain, ((v2_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('86', plain,
% 0.59/0.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 0.59/0.79      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.59/0.79  thf('87', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 0.59/0.79          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.59/0.79          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['67', '86'])).
% 0.59/0.79  thf('88', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79          | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 0.59/0.79          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.59/0.79          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['9', '87'])).
% 0.59/0.79  thf('89', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('90', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('91', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 0.59/0.79          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.59/0.79          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 0.59/0.79      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.59/0.79  thf('92', plain,
% 0.59/0.79      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B)
% 0.59/0.79        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['8', '91'])).
% 0.59/0.79  thf('93', plain,
% 0.59/0.79      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.59/0.79         ((m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.59/0.79          | ~ (zip_tseitin_0 @ X48 @ X49 @ X50))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.79  thf('94', plain,
% 0.59/0.79      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.59/0.79        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['92', '93'])).
% 0.59/0.79  thf('95', plain,
% 0.59/0.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.59/0.79        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 0.59/0.79        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('96', plain,
% 0.59/0.79      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.59/0.79         <= (~
% 0.59/0.79             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.59/0.79      inference('split', [status(esa)], ['95'])).
% 0.59/0.79  thf('97', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('98', plain,
% 0.59/0.79      (![X25 : $i]:
% 0.59/0.79         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 0.59/0.79          | ~ (v1_funct_1 @ X25)
% 0.59/0.79          | ~ (v1_relat_1 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.59/0.79  thf('99', plain,
% 0.59/0.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.59/0.79         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.59/0.79      inference('split', [status(esa)], ['95'])).
% 0.59/0.79  thf('100', plain,
% 0.59/0.79      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 0.59/0.79         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['98', '99'])).
% 0.59/0.79  thf('101', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('102', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.59/0.79      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.79  thf('103', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['97', '102'])).
% 0.59/0.79  thf('104', plain,
% 0.59/0.79      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B)
% 0.59/0.79        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['8', '91'])).
% 0.59/0.79  thf('105', plain,
% 0.59/0.79      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.59/0.79         ((v1_funct_2 @ X48 @ X50 @ X49) | ~ (zip_tseitin_0 @ X48 @ X49 @ X50))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.79  thf('106', plain,
% 0.59/0.79      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.59/0.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['104', '105'])).
% 0.59/0.79  thf('107', plain,
% 0.59/0.79      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('split', [status(esa)], ['95'])).
% 0.59/0.79  thf('108', plain,
% 0.59/0.79      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['106', '107'])).
% 0.59/0.79  thf('109', plain,
% 0.59/0.79      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['106', '107'])).
% 0.59/0.79  thf('110', plain,
% 0.59/0.79      (![X51 : $i, X52 : $i]:
% 0.59/0.79         (((X51) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X51 @ X52))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.79  thf('111', plain,
% 0.59/0.79      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['109', '110'])).
% 0.59/0.79  thf('112', plain,
% 0.59/0.79      (((zip_tseitin_1 @ k1_xboole_0 @ sk_B))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['108', '111'])).
% 0.59/0.79  thf('113', plain,
% 0.59/0.79      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['109', '110'])).
% 0.59/0.79  thf(t65_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.79         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.79  thf('114', plain,
% 0.59/0.79      (![X24 : $i]:
% 0.59/0.79         (((k1_relat_1 @ X24) != (k1_xboole_0))
% 0.59/0.79          | ((k2_relat_1 @ X24) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X24))),
% 0.59/0.79      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.59/0.79  thf('115', plain,
% 0.59/0.79      (((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.79         | ~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79         | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0))))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['113', '114'])).
% 0.59/0.79  thf('116', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('117', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf('118', plain,
% 0.59/0.79      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.59/0.79  thf('119', plain,
% 0.59/0.79      ((((sk_B) = (k1_xboole_0)))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['118'])).
% 0.59/0.79  thf('120', plain,
% 0.59/0.79      (((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.59/0.79         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['112', '119'])).
% 0.59/0.79  thf('121', plain,
% 0.59/0.79      (![X51 : $i, X52 : $i]:
% 0.59/0.79         (((X52) != (k1_xboole_0)) | ~ (zip_tseitin_1 @ X51 @ X52))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.79  thf('122', plain, (![X51 : $i]: ~ (zip_tseitin_1 @ X51 @ k1_xboole_0)),
% 0.59/0.79      inference('simplify', [status(thm)], ['121'])).
% 0.59/0.79  thf('123', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['120', '122'])).
% 0.59/0.79  thf('124', plain,
% 0.59/0.79      (~
% 0.59/0.79       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.59/0.79       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 0.59/0.79       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.59/0.79      inference('split', [status(esa)], ['95'])).
% 0.59/0.79  thf('125', plain,
% 0.59/0.79      (~
% 0.59/0.79       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.59/0.79      inference('sat_resolution*', [status(thm)], ['103', '123', '124'])).
% 0.59/0.79  thf('126', plain,
% 0.59/0.79      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.79      inference('simpl_trail', [status(thm)], ['96', '125'])).
% 0.59/0.79  thf('127', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.59/0.79      inference('clc', [status(thm)], ['94', '126'])).
% 0.59/0.79  thf('128', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.59/0.79      inference('clc', [status(thm)], ['94', '126'])).
% 0.59/0.79  thf('129', plain,
% 0.59/0.79      (![X51 : $i, X52 : $i]:
% 0.59/0.79         (((X51) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X51 @ X52))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.79  thf('130', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['128', '129'])).
% 0.59/0.79  thf('131', plain, ((zip_tseitin_1 @ k1_xboole_0 @ sk_B)),
% 0.59/0.79      inference('demod', [status(thm)], ['127', '130'])).
% 0.59/0.79  thf('132', plain,
% 0.59/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 0.59/0.79      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.59/0.79  thf('133', plain,
% 0.59/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.79         ((v1_relat_1 @ X27)
% 0.59/0.79          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.79  thf('134', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['132', '133'])).
% 0.59/0.79  thf('135', plain,
% 0.59/0.79      (![X26 : $i]:
% 0.59/0.79         (~ (v2_funct_1 @ X26)
% 0.59/0.79          | ((k1_relat_1 @ X26) = (k2_relat_1 @ (k2_funct_1 @ X26)))
% 0.59/0.79          | ~ (v1_funct_1 @ X26)
% 0.59/0.79          | ~ (v1_relat_1 @ X26))),
% 0.59/0.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.79  thf('136', plain,
% 0.59/0.79      (![X24 : $i]:
% 0.59/0.79         (((k2_relat_1 @ X24) != (k1_xboole_0))
% 0.59/0.79          | ((k1_relat_1 @ X24) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X24))),
% 0.59/0.79      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.59/0.79  thf('137', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_funct_1 @ X0)
% 0.59/0.79          | ~ (v2_funct_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.79          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['135', '136'])).
% 0.59/0.79  thf('138', plain,
% 0.59/0.79      ((((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0))
% 0.59/0.79        | ~ (v2_funct_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C_1)
% 0.59/0.79        | ~ (v1_relat_1 @ sk_C_1)
% 0.59/0.79        | ((k1_relat_1 @ sk_C_1) != (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['134', '137'])).
% 0.59/0.79  thf('139', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['44', '45', '46', '47', '48', '49'])).
% 0.59/0.79  thf('140', plain, ((v2_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('141', plain, ((v1_funct_1 @ sk_C_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('142', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('143', plain,
% 0.59/0.79      ((((sk_B) = (k1_xboole_0)) | ((k1_relat_1 @ sk_C_1) != (k1_xboole_0)))),
% 0.59/0.79      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 0.59/0.79  thf('144', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['128', '129'])).
% 0.59/0.79  thf('145', plain,
% 0.59/0.79      ((((sk_B) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.59/0.79      inference('demod', [status(thm)], ['143', '144'])).
% 0.59/0.79  thf('146', plain, (((sk_B) = (k1_xboole_0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['145'])).
% 0.59/0.79  thf('147', plain, ((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('demod', [status(thm)], ['131', '146'])).
% 0.59/0.79  thf('148', plain, (![X51 : $i]: ~ (zip_tseitin_1 @ X51 @ k1_xboole_0)),
% 0.59/0.79      inference('simplify', [status(thm)], ['121'])).
% 0.59/0.79  thf('149', plain, ($false), inference('sup-', [status(thm)], ['147', '148'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
