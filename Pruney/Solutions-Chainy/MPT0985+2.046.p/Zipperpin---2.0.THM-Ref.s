%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CtRqTDXwKR

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:33 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 612 expanded)
%              Number of leaves         :   46 ( 198 expanded)
%              Depth                    :   18
%              Number of atoms          :  910 (9217 expanded)
%              Number of equality atoms :   56 ( 324 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k3_relset_1 @ X28 @ X29 @ X27 )
        = ( k4_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('5',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_funct_1 @ X19 )
        = ( k4_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['5','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','16'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X38 ) ) )
      | ( v1_partfun1 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('19',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','16'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_partfun1 @ X33 @ X34 )
      | ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('22',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('25',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['31'])).

thf('35',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','16'])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['31'])).

thf('40',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['35','38','39'])).

thf('41',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['32','40'])).

thf('42',plain,(
    ~ ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(clc,[status(thm)],['30','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['19','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','16'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('59',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X30 @ ( k3_relset_1 @ X30 @ X31 @ X32 ) )
        = ( k2_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('60',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['5','15'])).

thf('62',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('65',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['32','40'])).

thf('68',plain,(
    ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['57','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','69'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('71',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('72',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('73',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','69'])).

thf('77',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('78',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['53','70','72','75','76','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['48','78'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('80',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('81',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['79','80'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['43','81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CtRqTDXwKR
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 352 iterations in 0.235s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.70  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.45/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.70  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.45/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.70  thf(t31_funct_2, conjecture,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.70           ( m1_subset_1 @
% 0.45/0.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.70          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.70            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.70              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.70              ( m1_subset_1 @
% 0.45/0.70                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.45/0.70    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.45/0.70  thf('0', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(dt_k3_relset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( m1_subset_1 @
% 0.45/0.70         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.45/0.70         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.45/0.70  thf('1', plain,
% 0.45/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (k3_relset_1 @ X21 @ X22 @ X23) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.45/0.70          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.45/0.70  thf('2', plain,
% 0.45/0.70      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.45/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.70  thf('3', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(redefinition_k3_relset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.45/0.70  thf('4', plain,
% 0.45/0.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.70         (((k3_relset_1 @ X28 @ X29 @ X27) = (k4_relat_1 @ X27))
% 0.45/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.45/0.70      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.45/0.70  thf('5', plain, (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.70  thf('6', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(cc2_relat_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.70  thf('7', plain,
% 0.45/0.70      (![X13 : $i, X14 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.45/0.70          | (v1_relat_1 @ X13)
% 0.45/0.70          | ~ (v1_relat_1 @ X14))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.70  thf('8', plain,
% 0.45/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.45/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.70  thf(fc6_relat_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.70  thf('9', plain,
% 0.45/0.70      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.70  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.70  thf(d9_funct_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.70       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.45/0.70  thf('11', plain,
% 0.45/0.70      (![X19 : $i]:
% 0.45/0.70         (~ (v2_funct_1 @ X19)
% 0.45/0.70          | ((k2_funct_1 @ X19) = (k4_relat_1 @ X19))
% 0.45/0.70          | ~ (v1_funct_1 @ X19)
% 0.45/0.70          | ~ (v1_relat_1 @ X19))),
% 0.45/0.70      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.45/0.70  thf('12', plain,
% 0.45/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.70        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.45/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.70  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('14', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('15', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.70      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.45/0.70  thf('16', plain,
% 0.45/0.70      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.45/0.70      inference('demod', [status(thm)], ['5', '15'])).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['2', '16'])).
% 0.45/0.70  thf(cc1_partfun1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( v1_xboole_0 @ A ) =>
% 0.45/0.70       ( ![C:$i]:
% 0.45/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.45/0.70  thf('18', plain,
% 0.45/0.70      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.70         (~ (v1_xboole_0 @ X36)
% 0.45/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X38)))
% 0.45/0.70          | (v1_partfun1 @ X37 @ X36))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.45/0.70  thf('19', plain,
% 0.45/0.70      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ sk_B) | ~ (v1_xboole_0 @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.70  thf('20', plain,
% 0.45/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['2', '16'])).
% 0.45/0.70  thf(cc1_funct_2, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.45/0.70         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.45/0.70  thf('21', plain,
% 0.45/0.70      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.70         (~ (v1_funct_1 @ X33)
% 0.45/0.70          | ~ (v1_partfun1 @ X33 @ X34)
% 0.45/0.70          | (v1_funct_2 @ X33 @ X34 @ X35)
% 0.45/0.70          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.45/0.70  thf('22', plain,
% 0.45/0.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.45/0.70        | ~ (v1_partfun1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 0.45/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.70  thf('23', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.70      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.45/0.70  thf(fc5_funct_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.45/0.70       ( ( v1_relat_1 @ ( k4_relat_1 @ A ) ) & 
% 0.45/0.70         ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.45/0.70  thf('24', plain,
% 0.45/0.70      (![X20 : $i]:
% 0.45/0.70         ((v1_funct_1 @ (k4_relat_1 @ X20))
% 0.45/0.70          | ~ (v2_funct_1 @ X20)
% 0.45/0.70          | ~ (v1_funct_1 @ X20)
% 0.45/0.70          | ~ (v1_relat_1 @ X20))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.45/0.70  thf('25', plain,
% 0.45/0.70      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.70      inference('sup+', [status(thm)], ['23', '24'])).
% 0.45/0.70  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.70      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.70  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('28', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('29', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.70      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.45/0.70  thf('30', plain,
% 0.45/0.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.45/0.70        | ~ (v1_partfun1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 0.45/0.70      inference('demod', [status(thm)], ['22', '29'])).
% 0.45/0.70  thf('31', plain,
% 0.45/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.45/0.70        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('32', plain,
% 0.45/0.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.45/0.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.70      inference('split', [status(esa)], ['31'])).
% 0.45/0.70  thf('33', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.70      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.45/0.70  thf('34', plain,
% 0.45/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.70         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.70      inference('split', [status(esa)], ['31'])).
% 0.45/0.70  thf('35', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.70  thf('36', plain,
% 0.45/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['2', '16'])).
% 0.45/0.70  thf('37', plain,
% 0.45/0.70      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.45/0.70         <= (~
% 0.45/0.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.45/0.70      inference('split', [status(esa)], ['31'])).
% 0.45/0.70  thf('38', plain,
% 0.45/0.70      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.70  thf('39', plain,
% 0.45/0.70      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.45/0.70       ~
% 0.45/0.70       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.45/0.70       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.70      inference('split', [status(esa)], ['31'])).
% 0.45/0.70  thf('40', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.45/0.70      inference('sat_resolution*', [status(thm)], ['35', '38', '39'])).
% 0.45/0.70  thf('41', plain, (~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.45/0.70      inference('simpl_trail', [status(thm)], ['32', '40'])).
% 0.45/0.70  thf('42', plain, (~ (v1_partfun1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 0.45/0.70      inference('clc', [status(thm)], ['30', '41'])).
% 0.45/0.70  thf('43', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.45/0.70      inference('clc', [status(thm)], ['19', '42'])).
% 0.45/0.70  thf('44', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.70  thf('45', plain,
% 0.45/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.70         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.45/0.70          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.45/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.70  thf('46', plain,
% 0.45/0.70      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.45/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.70  thf('47', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('48', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.45/0.70      inference('sup+', [status(thm)], ['46', '47'])).
% 0.45/0.70  thf('49', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(t3_subset, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.70  thf('50', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i]:
% 0.45/0.70         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.70  thf('51', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.70  thf(d10_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.70  thf('52', plain,
% 0.45/0.70      (![X0 : $i, X2 : $i]:
% 0.45/0.70         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.70  thf('53', plain,
% 0.45/0.70      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 0.45/0.70        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.70  thf(d1_funct_2, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_1, axiom,
% 0.45/0.70    (![B:$i,A:$i]:
% 0.45/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.70  thf('54', plain,
% 0.45/0.70      (![X39 : $i, X40 : $i]:
% 0.45/0.70         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.70  thf('55', plain,
% 0.45/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['2', '16'])).
% 0.45/0.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_3, axiom,
% 0.45/0.70    (![C:$i,B:$i,A:$i]:
% 0.45/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_5, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.70  thf('56', plain,
% 0.45/0.70      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.45/0.70         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.45/0.70          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.45/0.70          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.70  thf('57', plain,
% 0.45/0.70      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.45/0.70        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.70  thf('58', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(t24_relset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.45/0.70           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.45/0.70         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.45/0.70           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.70  thf('59', plain,
% 0.45/0.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.70         (((k1_relset_1 @ X31 @ X30 @ (k3_relset_1 @ X30 @ X31 @ X32))
% 0.45/0.70            = (k2_relset_1 @ X30 @ X31 @ X32))
% 0.45/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.45/0.70      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.45/0.70  thf('60', plain,
% 0.45/0.70      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.70         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.45/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.70  thf('61', plain,
% 0.45/0.70      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.45/0.70      inference('demod', [status(thm)], ['5', '15'])).
% 0.45/0.70  thf('62', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('63', plain,
% 0.45/0.70      (((k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_B))),
% 0.45/0.70      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.45/0.70  thf('64', plain,
% 0.45/0.70      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.45/0.70         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 0.45/0.70          | (v1_funct_2 @ X43 @ X41 @ X42)
% 0.45/0.70          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.70  thf('65', plain,
% 0.45/0.70      ((((sk_B) != (sk_B))
% 0.45/0.70        | ~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.45/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['63', '64'])).
% 0.45/0.70  thf('66', plain,
% 0.45/0.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.45/0.70        | ~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B))),
% 0.45/0.70      inference('simplify', [status(thm)], ['65'])).
% 0.45/0.70  thf('67', plain, (~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.45/0.70      inference('simpl_trail', [status(thm)], ['32', '40'])).
% 0.45/0.70  thf('68', plain, (~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)),
% 0.45/0.70      inference('clc', [status(thm)], ['66', '67'])).
% 0.45/0.70  thf('69', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B)),
% 0.45/0.70      inference('clc', [status(thm)], ['57', '68'])).
% 0.45/0.70  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['54', '69'])).
% 0.45/0.70  thf(t113_zfmisc_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.70  thf('71', plain,
% 0.45/0.70      (![X4 : $i, X5 : $i]:
% 0.45/0.70         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.70  thf('72', plain,
% 0.45/0.70      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.45/0.70      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.70  thf(t4_subset_1, axiom,
% 0.45/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.70  thf('73', plain,
% 0.45/0.70      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.45/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.70  thf('74', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i]:
% 0.45/0.70         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.70  thf('75', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.70  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['54', '69'])).
% 0.45/0.70  thf('77', plain,
% 0.45/0.70      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.45/0.70      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.70  thf('78', plain, (((k1_xboole_0) = (sk_C))),
% 0.45/0.70      inference('demod', [status(thm)], ['53', '70', '72', '75', '76', '77'])).
% 0.45/0.70  thf('79', plain, (((k2_relat_1 @ k1_xboole_0) = (sk_B))),
% 0.45/0.70      inference('demod', [status(thm)], ['48', '78'])).
% 0.45/0.70  thf(t60_relat_1, axiom,
% 0.45/0.70    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.70     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.71  thf('80', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.71      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.71  thf('81', plain, (((sk_B) = (k1_xboole_0))),
% 0.45/0.71      inference('sup+', [status(thm)], ['79', '80'])).
% 0.45/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.71  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.71  thf('83', plain, ($false),
% 0.45/0.71      inference('demod', [status(thm)], ['43', '81', '82'])).
% 0.45/0.71  
% 0.45/0.71  % SZS output end Refutation
% 0.45/0.71  
% 0.45/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
