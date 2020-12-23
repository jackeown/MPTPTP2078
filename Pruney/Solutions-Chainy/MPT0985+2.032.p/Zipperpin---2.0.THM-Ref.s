%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jehRMHKWK6

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:31 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  263 (3217 expanded)
%              Number of leaves         :   53 (1006 expanded)
%              Depth                    :   41
%              Number of atoms          : 1830 (47314 expanded)
%              Number of equality atoms :   89 (1561 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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

thf('20',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k1_relat_1 @ X29 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('21',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('22',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('23',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('24',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('43',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['26','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('56',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('57',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('58',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','59'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['22','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('65',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('69',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['20','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

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

thf('76',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ~ ( r1_tarski @ X56 @ X57 )
      | ( zip_tseitin_1 @ X56 @ X58 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ X58 @ X56 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X56 ) ) )
      | ( zip_tseitin_0 @ X59 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k1_relat_1 @ X29 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('79',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('80',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('81',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','59'])).

thf('82',plain,(
    ! [X50: $i] :
      ( ( v1_funct_2 @ X50 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('83',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('86',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['78','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('94',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['77','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('100',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A_1 @ sk_B )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','101'])).

thf('103',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( v1_funct_2 @ X51 @ X53 @ X52 )
      | ~ ( zip_tseitin_0 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('104',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('106',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('108',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('109',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('110',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('112',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['112'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('114',plain,(
    ! [X21: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('115',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('117',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('118',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('119',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['116','119'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('121',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('122',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('123',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['120','125'])).

thf('127',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('128',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k1_relat_1 @ X29 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('129',plain,(
    ! [X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['117','118'])).

thf(rc1_funct_1,axiom,(
    ? [A: $i] :
      ( ( v1_funct_1 @ A )
      & ( v1_relat_1 @ A ) ) )).

thf('135',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_funct_1])).

thf('136',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('137',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_funct_1])).

thf('141',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('143',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('144',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','134','141','144'])).

thf('146',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['11','113','146'])).

thf('148',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('149',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('150',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('153',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('156',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('157',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('158',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('159',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['158'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('160',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X47 ) ) )
      | ( v1_partfun1 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('161',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('163',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['162'])).

thf(rc1_relset_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( v1_xboole_0 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('164',plain,(
    ! [X48: $i,X49: $i] :
      ( m1_subset_1 @ ( sk_C @ X48 @ X49 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('167',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( sk_C @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X48: $i,X49: $i] :
      ( v1_xboole_0 @ ( sk_C @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('171',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['161','171'])).

thf('173',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['157','172'])).

thf('174',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('175',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_partfun1 @ X42 @ X43 )
      | ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['139','140'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['173','178'])).

thf('180',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 ),
    inference(demod,[status(thm)],['147','154','179'])).

thf('181',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('182',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','180','181'])).

thf('183',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','182'])).

thf('184',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('185',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('186',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('188',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('191',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('193',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A_1 @ sk_B )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','101'])).

thf('195',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ~ ( zip_tseitin_0 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('196',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','182'])).

thf('198',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('200',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['158'])).

thf('202',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('203',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['198','199'])).

thf('204',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['158'])).

thf('205',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['193','200','201','202','203','204'])).

thf('206',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['145'])).

thf('207',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('208',plain,(
    $false ),
    inference(demod,[status(thm)],['183','205','206','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jehRMHKWK6
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 863 iterations in 0.255s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.52/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.52/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.52/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.52/0.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.52/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.71  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.52/0.71  thf(t31_funct_2, conjecture,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.71       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.52/0.71         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.52/0.71           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.52/0.71           ( m1_subset_1 @
% 0.52/0.71             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.71            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.71          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.52/0.71            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.52/0.71              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.52/0.71              ( m1_subset_1 @
% 0.52/0.71                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)
% 0.52/0.71        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))
% 0.52/0.71         <= (~
% 0.52/0.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(cc1_relset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( v1_relat_1 @ C ) ))).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.71         ((v1_relat_1 @ X30)
% 0.52/0.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.52/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.71  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf(dt_k2_funct_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.52/0.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 0.52/0.71          | ~ (v1_funct_1 @ X26)
% 0.52/0.71          | ~ (v1_relat_1 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.52/0.71         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 0.52/0.71         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.71  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.52/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.52/0.71  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['4', '9'])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1))
% 0.52/0.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(cc2_relset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.71         ((v4_relat_1 @ X33 @ X34)
% 0.52/0.71          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.52/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.71  thf('14', plain, ((v4_relat_1 @ sk_C_1 @ sk_A_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.71  thf(d18_relat_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ B ) =>
% 0.52/0.71       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X16 : $i, X17 : $i]:
% 0.52/0.71         (~ (v4_relat_1 @ X16 @ X17)
% 0.52/0.71          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.52/0.71          | ~ (v1_relat_1 @ X16))),
% 0.52/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.71  thf('16', plain,
% 0.52/0.71      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.71  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A_1)),
% 0.52/0.71      inference('demod', [status(thm)], ['16', '17'])).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 0.52/0.71          | ~ (v1_funct_1 @ X26)
% 0.52/0.71          | ~ (v1_relat_1 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.71  thf(t55_funct_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.71       ( ( v2_funct_1 @ A ) =>
% 0.52/0.71         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.52/0.71           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      (![X29 : $i]:
% 0.52/0.71         (~ (v2_funct_1 @ X29)
% 0.52/0.71          | ((k1_relat_1 @ X29) = (k2_relat_1 @ (k2_funct_1 @ X29)))
% 0.52/0.71          | ~ (v1_funct_1 @ X29)
% 0.52/0.71          | ~ (v1_relat_1 @ X29))),
% 0.52/0.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 0.52/0.71          | ~ (v1_funct_1 @ X26)
% 0.52/0.71          | ~ (v1_relat_1 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.71  thf('22', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 0.52/0.71          | ~ (v1_funct_1 @ X26)
% 0.52/0.71          | ~ (v1_relat_1 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X29 : $i]:
% 0.52/0.71         (~ (v2_funct_1 @ X29)
% 0.52/0.71          | ((k2_relat_1 @ X29) = (k1_relat_1 @ (k2_funct_1 @ X29)))
% 0.52/0.71          | ~ (v1_funct_1 @ X29)
% 0.52/0.71          | ~ (v1_relat_1 @ X29))),
% 0.52/0.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 0.52/0.71          | ~ (v1_funct_1 @ X26)
% 0.52/0.71          | ~ (v1_relat_1 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.71  thf(d10_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.71  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.71      inference('simplify', [status(thm)], ['25'])).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 0.52/0.71          | ~ (v1_funct_1 @ X26)
% 0.52/0.71          | ~ (v1_relat_1 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.52/0.71         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 0.52/0.71          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.71  thf('31', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1) = (sk_B))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('32', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.52/0.71      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (![X29 : $i]:
% 0.52/0.71         (~ (v2_funct_1 @ X29)
% 0.52/0.71          | ((k2_relat_1 @ X29) = (k1_relat_1 @ (k2_funct_1 @ X29)))
% 0.52/0.71          | ~ (v1_funct_1 @ X29)
% 0.52/0.71          | ~ (v1_relat_1 @ X29))),
% 0.52/0.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (![X16 : $i, X17 : $i]:
% 0.52/0.71         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.52/0.71          | (v4_relat_1 @ X16 @ X17)
% 0.52/0.71          | ~ (v1_relat_1 @ X16))),
% 0.52/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.52/0.71          | ~ (v1_relat_1 @ X0)
% 0.52/0.71          | ~ (v1_funct_1 @ X0)
% 0.52/0.71          | ~ (v2_funct_1 @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.71          | (v4_relat_1 @ (k2_funct_1 @ X0) @ X1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.71  thf('36', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (r1_tarski @ sk_B @ X0)
% 0.52/0.71          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71          | ~ (v2_funct_1 @ sk_C_1)
% 0.52/0.71          | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71          | ~ (v1_relat_1 @ sk_C_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['32', '35'])).
% 0.52/0.71  thf('37', plain, ((v2_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('40', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (r1_tarski @ sk_B @ X0)
% 0.52/0.71          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 0.52/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.52/0.71      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71          | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 0.52/0.71          | ~ (r1_tarski @ sk_B @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['27', '40'])).
% 0.52/0.71  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('43', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.52/0.71  thf('45', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B)),
% 0.52/0.71      inference('sup-', [status(thm)], ['26', '44'])).
% 0.52/0.71  thf('46', plain,
% 0.52/0.71      (![X16 : $i, X17 : $i]:
% 0.52/0.71         (~ (v4_relat_1 @ X16 @ X17)
% 0.52/0.71          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.52/0.71          | ~ (v1_relat_1 @ X16))),
% 0.52/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.71  thf('47', plain,
% 0.52/0.71      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('48', plain,
% 0.52/0.71      ((~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['24', '47'])).
% 0.52/0.71  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('50', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('51', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B)),
% 0.52/0.71      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.52/0.71  thf('52', plain,
% 0.52/0.71      (![X0 : $i, X2 : $i]:
% 0.52/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.52/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.71  thf('53', plain,
% 0.52/0.71      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.52/0.71        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['51', '52'])).
% 0.52/0.71  thf('54', plain,
% 0.52/0.71      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.52/0.71        | ~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71        | ~ (v2_funct_1 @ sk_C_1)
% 0.52/0.71        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['23', '53'])).
% 0.52/0.71  thf('55', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.52/0.71      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.71  thf('56', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.71      inference('simplify', [status(thm)], ['25'])).
% 0.52/0.71  thf('57', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('58', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('59', plain, ((v2_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('60', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.52/0.71      inference('demod', [status(thm)], ['54', '55', '56', '57', '58', '59'])).
% 0.52/0.71  thf(t3_funct_2, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.71       ( ( v1_funct_1 @ A ) & 
% 0.52/0.71         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.52/0.71         ( m1_subset_1 @
% 0.52/0.71           A @ 
% 0.52/0.71           ( k1_zfmisc_1 @
% 0.52/0.71             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.52/0.71  thf('61', plain,
% 0.52/0.71      (![X50 : $i]:
% 0.52/0.71         ((m1_subset_1 @ X50 @ 
% 0.52/0.71           (k1_zfmisc_1 @ 
% 0.52/0.71            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 0.52/0.71          | ~ (v1_funct_1 @ X50)
% 0.52/0.71          | ~ (v1_relat_1 @ X50))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71         (k1_zfmisc_1 @ 
% 0.52/0.71          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 0.52/0.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['60', '61'])).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      ((~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71           (k1_zfmisc_1 @ 
% 0.52/0.71            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['22', '62'])).
% 0.52/0.71  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('65', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('66', plain,
% 0.52/0.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71           (k1_zfmisc_1 @ 
% 0.52/0.71            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 0.52/0.71      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      ((~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71           (k1_zfmisc_1 @ 
% 0.52/0.71            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['21', '66'])).
% 0.52/0.71  thf('68', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('69', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('70', plain,
% 0.52/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71        (k1_zfmisc_1 @ 
% 0.52/0.71         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 0.52/0.71      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.52/0.71  thf('71', plain,
% 0.52/0.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))
% 0.52/0.71        | ~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71        | ~ (v2_funct_1 @ sk_C_1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['20', '70'])).
% 0.52/0.71  thf('72', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('74', plain, ((v2_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.52/0.71      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.52/0.71  thf(t9_funct_2, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.71     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.71         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.52/0.71       ( ( r1_tarski @ B @ C ) =>
% 0.52/0.71         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.52/0.71             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.52/0.71           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.52/0.71  thf(zf_stmt_2, axiom,
% 0.52/0.71    (![B:$i,A:$i]:
% 0.52/0.71     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.52/0.71       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.52/0.71  thf(zf_stmt_4, axiom,
% 0.52/0.71    (![D:$i,C:$i,A:$i]:
% 0.52/0.71     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.52/0.71       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.52/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_5, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.71       ( ( r1_tarski @ B @ C ) =>
% 0.52/0.71         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.52/0.71  thf('76', plain,
% 0.52/0.71      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.52/0.71         (~ (r1_tarski @ X56 @ X57)
% 0.52/0.71          | (zip_tseitin_1 @ X56 @ X58)
% 0.52/0.71          | ~ (v1_funct_1 @ X59)
% 0.52/0.71          | ~ (v1_funct_2 @ X59 @ X58 @ X56)
% 0.52/0.71          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X56)))
% 0.52/0.71          | (zip_tseitin_0 @ X59 @ X57 @ X58))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 0.52/0.71          | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.71               (k1_relat_1 @ sk_C_1))
% 0.52/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.52/0.71          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['75', '76'])).
% 0.52/0.71  thf('78', plain,
% 0.52/0.71      (![X29 : $i]:
% 0.52/0.71         (~ (v2_funct_1 @ X29)
% 0.52/0.71          | ((k1_relat_1 @ X29) = (k2_relat_1 @ (k2_funct_1 @ X29)))
% 0.52/0.71          | ~ (v1_funct_1 @ X29)
% 0.52/0.71          | ~ (v1_relat_1 @ X29))),
% 0.52/0.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.52/0.71  thf('79', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 0.52/0.71          | ~ (v1_funct_1 @ X26)
% 0.52/0.71          | ~ (v1_relat_1 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.71  thf('80', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 0.52/0.71          | ~ (v1_funct_1 @ X26)
% 0.52/0.71          | ~ (v1_relat_1 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.71  thf('81', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.52/0.71      inference('demod', [status(thm)], ['54', '55', '56', '57', '58', '59'])).
% 0.52/0.71  thf('82', plain,
% 0.52/0.71      (![X50 : $i]:
% 0.52/0.71         ((v1_funct_2 @ X50 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))
% 0.52/0.71          | ~ (v1_funct_1 @ X50)
% 0.52/0.71          | ~ (v1_relat_1 @ X50))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.52/0.71  thf('83', plain,
% 0.52/0.71      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.71         (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.52/0.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['81', '82'])).
% 0.52/0.71  thf('84', plain,
% 0.52/0.71      ((~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.71           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['80', '83'])).
% 0.52/0.71  thf('85', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('86', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('87', plain,
% 0.52/0.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.71           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.52/0.71      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.52/0.71  thf('88', plain,
% 0.52/0.71      ((~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.71           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['79', '87'])).
% 0.52/0.71  thf('89', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('90', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('91', plain,
% 0.52/0.71      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.71        (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.52/0.71      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.52/0.71  thf('92', plain,
% 0.52/0.71      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))
% 0.52/0.71        | ~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71        | ~ (v2_funct_1 @ sk_C_1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['78', '91'])).
% 0.52/0.71  thf('93', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('94', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('95', plain, ((v2_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('96', plain,
% 0.52/0.71      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 0.52/0.71      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.52/0.71  thf('97', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 0.52/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.52/0.71          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.52/0.71          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['77', '96'])).
% 0.52/0.71  thf('98', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71          | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 0.52/0.71          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.52/0.71          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['19', '97'])).
% 0.52/0.71  thf('99', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('100', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('101', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 0.52/0.71          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.52/0.71          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.52/0.71  thf('102', plain,
% 0.52/0.71      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ sk_A_1 @ sk_B)
% 0.52/0.71        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['18', '101'])).
% 0.52/0.71  thf('103', plain,
% 0.52/0.71      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.52/0.71         ((v1_funct_2 @ X51 @ X53 @ X52) | ~ (zip_tseitin_0 @ X51 @ X52 @ X53))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.52/0.71  thf('104', plain,
% 0.52/0.71      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.52/0.71        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['102', '103'])).
% 0.52/0.71  thf('105', plain,
% 0.52/0.71      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1))
% 0.52/0.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('106', plain,
% 0.52/0.71      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))
% 0.52/0.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['104', '105'])).
% 0.52/0.71  thf('107', plain,
% 0.52/0.71      (![X54 : $i, X55 : $i]:
% 0.52/0.71         (((X54) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X54 @ X55))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.71  thf('108', plain,
% 0.52/0.71      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.52/0.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['106', '107'])).
% 0.52/0.71  thf(t64_relat_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ A ) =>
% 0.52/0.71       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.71           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.71         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.71  thf('109', plain,
% 0.52/0.71      (![X22 : $i]:
% 0.52/0.71         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.52/0.71          | ((X22) = (k1_xboole_0))
% 0.52/0.71          | ~ (v1_relat_1 @ X22))),
% 0.52/0.71      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.52/0.71  thf('110', plain,
% 0.52/0.71      (((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.71         | ~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71         | ((sk_C_1) = (k1_xboole_0))))
% 0.52/0.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['108', '109'])).
% 0.52/0.71  thf('111', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('112', plain,
% 0.52/0.71      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0))))
% 0.52/0.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.71      inference('demod', [status(thm)], ['110', '111'])).
% 0.52/0.71  thf('113', plain,
% 0.52/0.71      ((((sk_C_1) = (k1_xboole_0)))
% 0.52/0.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['112'])).
% 0.52/0.71  thf(l222_relat_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.52/0.71  thf('114', plain, (![X21 : $i]: (v4_relat_1 @ k1_xboole_0 @ X21)),
% 0.52/0.71      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.52/0.71  thf('115', plain,
% 0.52/0.71      (![X16 : $i, X17 : $i]:
% 0.52/0.71         (~ (v4_relat_1 @ X16 @ X17)
% 0.52/0.71          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.52/0.71          | ~ (v1_relat_1 @ X16))),
% 0.52/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.71  thf('116', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.71          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['114', '115'])).
% 0.52/0.71  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.52/0.71  thf('117', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.52/0.71  thf(fc4_funct_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.52/0.71       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.52/0.71  thf('118', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.52/0.71      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.52/0.71  thf('119', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.71      inference('sup+', [status(thm)], ['117', '118'])).
% 0.52/0.71  thf('120', plain,
% 0.52/0.71      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.52/0.71      inference('demod', [status(thm)], ['116', '119'])).
% 0.52/0.71  thf(t4_subset_1, axiom,
% 0.52/0.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.71  thf('121', plain,
% 0.52/0.71      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.52/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.71  thf(t3_subset, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.71  thf('122', plain,
% 0.52/0.71      (![X7 : $i, X8 : $i]:
% 0.52/0.71         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('123', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['121', '122'])).
% 0.52/0.71  thf('124', plain,
% 0.52/0.71      (![X0 : $i, X2 : $i]:
% 0.52/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.52/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.71  thf('125', plain,
% 0.52/0.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['123', '124'])).
% 0.52/0.71  thf('126', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['120', '125'])).
% 0.52/0.71  thf('127', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 0.52/0.71          | ~ (v1_funct_1 @ X26)
% 0.52/0.71          | ~ (v1_relat_1 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.71  thf('128', plain,
% 0.52/0.71      (![X29 : $i]:
% 0.52/0.71         (~ (v2_funct_1 @ X29)
% 0.52/0.72          | ((k1_relat_1 @ X29) = (k2_relat_1 @ (k2_funct_1 @ X29)))
% 0.52/0.72          | ~ (v1_funct_1 @ X29)
% 0.52/0.72          | ~ (v1_relat_1 @ X29))),
% 0.52/0.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.52/0.72  thf('129', plain,
% 0.52/0.72      (![X22 : $i]:
% 0.52/0.72         (((k2_relat_1 @ X22) != (k1_xboole_0))
% 0.52/0.72          | ((X22) = (k1_xboole_0))
% 0.52/0.72          | ~ (v1_relat_1 @ X22))),
% 0.52/0.72      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.52/0.72  thf('130', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_funct_1 @ X0)
% 0.52/0.72          | ~ (v2_funct_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.72          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['128', '129'])).
% 0.52/0.72  thf('131', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_funct_1 @ X0)
% 0.52/0.72          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 0.52/0.72          | ~ (v2_funct_1 @ X0)
% 0.52/0.72          | ~ (v1_funct_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ((k1_relat_1 @ X0) != (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['127', '130'])).
% 0.52/0.72  thf('132', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.52/0.72          | ~ (v2_funct_1 @ X0)
% 0.52/0.72          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 0.52/0.72          | ~ (v1_funct_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ X0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['131'])).
% 0.52/0.72  thf('133', plain,
% 0.52/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.72        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.72        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.52/0.72        | ((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.72        | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['126', '132'])).
% 0.52/0.72  thf('134', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.72      inference('sup+', [status(thm)], ['117', '118'])).
% 0.52/0.72  thf(rc1_funct_1, axiom,
% 0.52/0.72    (?[A:$i]: ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ))).
% 0.52/0.72  thf('135', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [rc1_funct_1])).
% 0.52/0.72  thf('136', plain,
% 0.52/0.72      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.72  thf(cc3_funct_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 0.52/0.72  thf('137', plain,
% 0.52/0.72      (![X24 : $i, X25 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.52/0.72          | (v1_funct_1 @ X24)
% 0.52/0.72          | ~ (v1_funct_1 @ X25)
% 0.52/0.72          | ~ (v1_relat_1 @ X25))),
% 0.52/0.72      inference('cnf', [status(esa)], [cc3_funct_1])).
% 0.52/0.72  thf('138', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_funct_1 @ X0)
% 0.52/0.72          | (v1_funct_1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['136', '137'])).
% 0.52/0.72  thf('139', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_funct_1 @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['135', '138'])).
% 0.52/0.72  thf('140', plain, ((v1_funct_1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [rc1_funct_1])).
% 0.52/0.72  thf('141', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['139', '140'])).
% 0.52/0.72  thf('142', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.52/0.72  thf('143', plain, (![X28 : $i]: (v2_funct_1 @ (k6_relat_1 @ X28))),
% 0.52/0.72      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.52/0.72  thf('144', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.52/0.72      inference('sup+', [status(thm)], ['142', '143'])).
% 0.52/0.72  thf('145', plain,
% 0.52/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.72        | ((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.72      inference('demod', [status(thm)], ['133', '134', '141', '144'])).
% 0.52/0.72  thf('146', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['145'])).
% 0.52/0.72  thf('147', plain,
% 0.52/0.72      ((~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A_1))
% 0.52/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.72      inference('demod', [status(thm)], ['11', '113', '146'])).
% 0.52/0.72  thf('148', plain,
% 0.52/0.72      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.52/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['106', '107'])).
% 0.52/0.72  thf(t65_relat_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_relat_1 @ A ) =>
% 0.52/0.72       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.72         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.72  thf('149', plain,
% 0.52/0.72      (![X23 : $i]:
% 0.52/0.72         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.52/0.72          | ((k2_relat_1 @ X23) = (k1_xboole_0))
% 0.52/0.72          | ~ (v1_relat_1 @ X23))),
% 0.52/0.72      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.52/0.72  thf('150', plain,
% 0.52/0.72      (((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.72         | ~ (v1_relat_1 @ sk_C_1)
% 0.52/0.72         | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0))))
% 0.52/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['148', '149'])).
% 0.52/0.72  thf('151', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf('152', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.52/0.72      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.72  thf('153', plain,
% 0.52/0.72      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.52/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.72      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.52/0.72  thf('154', plain,
% 0.52/0.72      ((((sk_B) = (k1_xboole_0)))
% 0.52/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['153'])).
% 0.52/0.72  thf('155', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.72      inference('simplify', [status(thm)], ['25'])).
% 0.52/0.72  thf('156', plain,
% 0.52/0.72      (![X7 : $i, X9 : $i]:
% 0.52/0.72         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.72  thf('157', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['155', '156'])).
% 0.52/0.72  thf(t113_zfmisc_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.72  thf('158', plain,
% 0.52/0.72      (![X4 : $i, X5 : $i]:
% 0.52/0.72         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.72  thf('159', plain,
% 0.52/0.72      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['158'])).
% 0.52/0.72  thf(cc1_partfun1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( v1_xboole_0 @ A ) =>
% 0.52/0.72       ( ![C:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.72           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.52/0.72  thf('160', plain,
% 0.52/0.72      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.52/0.72         (~ (v1_xboole_0 @ X45)
% 0.52/0.72          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X47)))
% 0.52/0.72          | (v1_partfun1 @ X46 @ X45))),
% 0.52/0.72      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.52/0.72  thf('161', plain,
% 0.52/0.72      (![X1 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.72          | (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.52/0.72          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['159', '160'])).
% 0.52/0.72  thf('162', plain,
% 0.52/0.72      (![X4 : $i, X5 : $i]:
% 0.52/0.72         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.72  thf('163', plain,
% 0.52/0.72      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['162'])).
% 0.52/0.72  thf(rc1_relset_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ?[C:$i]:
% 0.52/0.72       ( ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 0.52/0.72         ( v1_relat_1 @ C ) & ( v1_xboole_0 @ C ) & 
% 0.52/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.52/0.72  thf('164', plain,
% 0.52/0.72      (![X48 : $i, X49 : $i]:
% 0.52/0.72         (m1_subset_1 @ (sk_C @ X48 @ X49) @ 
% 0.52/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))),
% 0.52/0.72      inference('cnf', [status(esa)], [rc1_relset_1])).
% 0.52/0.72  thf('165', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['163', '164'])).
% 0.52/0.72  thf('166', plain,
% 0.52/0.72      (![X7 : $i, X8 : $i]:
% 0.52/0.72         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.72  thf('167', plain,
% 0.52/0.72      (![X0 : $i]: (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.52/0.72      inference('sup-', [status(thm)], ['165', '166'])).
% 0.52/0.72  thf('168', plain,
% 0.52/0.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['123', '124'])).
% 0.52/0.72  thf('169', plain, (![X0 : $i]: ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['167', '168'])).
% 0.52/0.72  thf('170', plain,
% 0.52/0.72      (![X48 : $i, X49 : $i]: (v1_xboole_0 @ (sk_C @ X48 @ X49))),
% 0.52/0.72      inference('cnf', [status(esa)], [rc1_relset_1])).
% 0.52/0.72  thf('171', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('sup+', [status(thm)], ['169', '170'])).
% 0.52/0.72  thf('172', plain,
% 0.52/0.72      (![X1 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.52/0.72          | (v1_partfun1 @ X1 @ k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['161', '171'])).
% 0.52/0.72  thf('173', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('sup-', [status(thm)], ['157', '172'])).
% 0.52/0.72  thf('174', plain,
% 0.52/0.72      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.72  thf(cc1_funct_2, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.72       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.52/0.72         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.52/0.72  thf('175', plain,
% 0.52/0.72      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.52/0.72         (~ (v1_funct_1 @ X42)
% 0.52/0.72          | ~ (v1_partfun1 @ X42 @ X43)
% 0.52/0.72          | (v1_funct_2 @ X42 @ X43 @ X44)
% 0.52/0.72          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.52/0.72      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.52/0.72  thf('176', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.52/0.72          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 0.52/0.72          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['174', '175'])).
% 0.52/0.72  thf('177', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['139', '140'])).
% 0.52/0.72  thf('178', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.52/0.72          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 0.52/0.72      inference('demod', [status(thm)], ['176', '177'])).
% 0.52/0.72  thf('179', plain,
% 0.52/0.72      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.52/0.72      inference('sup-', [status(thm)], ['173', '178'])).
% 0.52/0.72  thf('180', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1))),
% 0.52/0.72      inference('demod', [status(thm)], ['147', '154', '179'])).
% 0.52/0.72  thf('181', plain,
% 0.52/0.72      (~
% 0.52/0.72       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))) | 
% 0.52/0.72       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A_1)) | 
% 0.52/0.72       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('182', plain,
% 0.52/0.72      (~
% 0.52/0.72       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 0.52/0.72      inference('sat_resolution*', [status(thm)], ['10', '180', '181'])).
% 0.52/0.72  thf('183', plain,
% 0.52/0.72      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 0.52/0.72      inference('simpl_trail', [status(thm)], ['1', '182'])).
% 0.52/0.72  thf('184', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.52/0.72      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.72  thf('185', plain,
% 0.52/0.72      (![X50 : $i]:
% 0.52/0.72         ((m1_subset_1 @ X50 @ 
% 0.52/0.72           (k1_zfmisc_1 @ 
% 0.52/0.72            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 0.52/0.72          | ~ (v1_funct_1 @ X50)
% 0.52/0.72          | ~ (v1_relat_1 @ X50))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.52/0.72  thf('186', plain,
% 0.52/0.72      (((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))
% 0.52/0.72        | ~ (v1_relat_1 @ sk_C_1)
% 0.52/0.72        | ~ (v1_funct_1 @ sk_C_1))),
% 0.52/0.72      inference('sup+', [status(thm)], ['184', '185'])).
% 0.52/0.72  thf('187', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf('188', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('189', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.52/0.72  thf('190', plain,
% 0.52/0.72      (![X7 : $i, X8 : $i]:
% 0.52/0.72         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.72  thf('191', plain,
% 0.52/0.72      ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.52/0.72      inference('sup-', [status(thm)], ['189', '190'])).
% 0.52/0.72  thf('192', plain,
% 0.52/0.72      (![X0 : $i, X2 : $i]:
% 0.52/0.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.52/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.72  thf('193', plain,
% 0.52/0.72      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B) @ sk_C_1)
% 0.52/0.72        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B) = (sk_C_1)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['191', '192'])).
% 0.52/0.72  thf('194', plain,
% 0.52/0.72      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ sk_A_1 @ sk_B)
% 0.52/0.72        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.52/0.72      inference('sup-', [status(thm)], ['18', '101'])).
% 0.52/0.72  thf('195', plain,
% 0.52/0.72      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.52/0.72         ((m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 0.52/0.72          | ~ (zip_tseitin_0 @ X51 @ X52 @ X53))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.52/0.72  thf('196', plain,
% 0.52/0.72      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.52/0.72        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['194', '195'])).
% 0.52/0.72  thf('197', plain,
% 0.52/0.72      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.52/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 0.52/0.72      inference('simpl_trail', [status(thm)], ['1', '182'])).
% 0.52/0.72  thf('198', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.52/0.72      inference('clc', [status(thm)], ['196', '197'])).
% 0.52/0.72  thf('199', plain,
% 0.52/0.72      (![X54 : $i, X55 : $i]:
% 0.52/0.72         (((X54) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X54 @ X55))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.72  thf('200', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['198', '199'])).
% 0.52/0.72  thf('201', plain,
% 0.52/0.72      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['158'])).
% 0.52/0.72  thf('202', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.52/0.72      inference('sup-', [status(thm)], ['121', '122'])).
% 0.52/0.72  thf('203', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['198', '199'])).
% 0.52/0.72  thf('204', plain,
% 0.52/0.72      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['158'])).
% 0.52/0.72  thf('205', plain, (((k1_xboole_0) = (sk_C_1))),
% 0.52/0.72      inference('demod', [status(thm)],
% 0.52/0.72                ['193', '200', '201', '202', '203', '204'])).
% 0.52/0.72  thf('206', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['145'])).
% 0.52/0.72  thf('207', plain,
% 0.52/0.72      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.72  thf('208', plain, ($false),
% 0.52/0.72      inference('demod', [status(thm)], ['183', '205', '206', '207'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
