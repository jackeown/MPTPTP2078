%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QfSruaPxe0

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:09 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  281 (2442 expanded)
%              Number of leaves         :   46 ( 742 expanded)
%              Depth                    :   28
%              Number of atoms          : 2532 (53907 expanded)
%              Number of equality atoms :  135 (1728 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X19 ) )
        = X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('3',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X23 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','22','23'])).

thf('25',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','22','23'])).

thf('26',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','22','23'])).

thf('27',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','24','25','26'])).

thf('28',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('33',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k2_relset_1 @ X45 @ X44 @ X46 )
       != X44 )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_tops_2 @ X45 @ X44 @ X46 )
        = ( k2_funct_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','40','41','46'])).

thf('48',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['27','48'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X16: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('51',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('53',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X19 ) )
        = X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X16: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t31_funct_2,axiom,(
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

thf('64',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k2_relset_1 @ X36 @ X35 @ X34 )
       != X35 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('68',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X23 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('73',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('75',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('76',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('80',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ X41 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('86',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k2_relset_1 @ X36 @ X35 @ X34 )
       != X35 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('90',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('91',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','84','93'])).

thf('95',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('97',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('98',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('101',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ( ( k5_relat_1 @ X38 @ ( k2_funct_1 @ X38 ) )
        = ( k6_partfun1 @ X39 ) )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relset_1 @ X39 @ X37 @ X38 )
       != X37 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('102',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ( ( k5_relat_1 @ X38 @ ( k2_funct_1 @ X38 ) )
        = ( k6_relat_1 @ X39 ) )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relset_1 @ X39 @ X37 @ X38 )
       != X37 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('111',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('112',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('113',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','116','117','118'])).

thf('120',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','22','23'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('124',plain,(
    ! [X43: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('125',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','129'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('131',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('132',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('138',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','138'])).

thf('140',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('141',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['94','142'])).

thf('144',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k2_relset_1 @ X45 @ X44 @ X46 )
       != X44 )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_tops_2 @ X45 @ X44 @ X46 )
        = ( k2_funct_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('147',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('148',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ( v1_funct_2 @ X40 @ ( k1_relat_1 @ X40 ) @ X41 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('151',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('152',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('154',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('156',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('157',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('158',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('162',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['155','162'])).

thf('164',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('165',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167','168'])).

thf('170',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('171',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ X41 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['169','174'])).

thf('176',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167','168'])).

thf('177',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('178',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('179',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['145','146','154','179'])).

thf('181',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['61','186'])).

thf('188',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('189',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('190',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('192',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['187','192','193','194','195'])).

thf('197',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['49','196'])).

thf('198',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','197'])).

thf('199',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('200',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('201',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['199','204'])).

thf('206',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('209',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_funct_2 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('215',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('216',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['213','214','215','216'])).

thf('218',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['207','217'])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('221',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('222',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['221','222'])).

thf('224',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['220','225'])).

thf('227',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['218','219','228'])).

thf('230',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('231',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    $false ),
    inference(demod,[status(thm)],['198','229','230','231','232'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QfSruaPxe0
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 551 iterations in 0.164s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.39/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.39/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.62  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.39/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.39/0.62  thf(t65_funct_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      (![X19 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X19)
% 0.39/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X19)) = (X19))
% 0.39/0.62          | ~ (v1_funct_1 @ X19)
% 0.39/0.62          | ~ (v1_relat_1 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.39/0.62  thf(d3_struct_0, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf(t64_tops_2, conjecture,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( l1_struct_0 @ A ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.62                 ( m1_subset_1 @
% 0.39/0.62                   C @ 
% 0.39/0.62                   ( k1_zfmisc_1 @
% 0.39/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.62               ( ( ( ( k2_relset_1 @
% 0.39/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.39/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.39/0.62                 ( r2_funct_2 @
% 0.39/0.62                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.39/0.62                   ( k2_tops_2 @
% 0.39/0.62                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.62                     ( k2_tops_2 @
% 0.39/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.39/0.62                   C ) ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i]:
% 0.39/0.62        ( ( l1_struct_0 @ A ) =>
% 0.39/0.62          ( ![B:$i]:
% 0.39/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.39/0.62              ( ![C:$i]:
% 0.39/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.62                    ( v1_funct_2 @
% 0.39/0.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.62                    ( m1_subset_1 @
% 0.39/0.62                      C @ 
% 0.39/0.62                      ( k1_zfmisc_1 @
% 0.39/0.62                        ( k2_zfmisc_1 @
% 0.39/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.62                  ( ( ( ( k2_relset_1 @
% 0.39/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.62                        ( k2_struct_0 @ B ) ) & 
% 0.39/0.62                      ( v2_funct_1 @ C ) ) =>
% 0.39/0.62                    ( r2_funct_2 @
% 0.39/0.62                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.39/0.62                      ( k2_tops_2 @
% 0.39/0.62                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.62                        ( k2_tops_2 @
% 0.39/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.39/0.62                      C ) ) ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.62          sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.62           sk_C)
% 0.39/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.62          sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.62           sk_C)
% 0.39/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '6'])).
% 0.39/0.62  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.62          sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(dt_k2_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.62         ((m1_subset_1 @ (k2_relset_1 @ X23 @ X24 @ X25) @ (k1_zfmisc_1 @ X24))
% 0.39/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      ((m1_subset_1 @ 
% 0.39/0.62        (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.39/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.62  thf(t3_subset, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('17', plain, ((r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.62  thf(d10_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X0 : $i, X2 : $i]:
% 0.39/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.39/0.62        | ((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.39/0.62        | ((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['10', '19'])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.62  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('24', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['20', '22', '23'])).
% 0.39/0.62  thf('25', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['20', '22', '23'])).
% 0.39/0.62  thf('26', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['20', '22', '23'])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.39/0.62          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.62          sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '24', '25', '26'])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_C @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf(d4_tops_2, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.39/0.62         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.39/0.62         (((k2_relset_1 @ X45 @ X44 @ X46) != (X44))
% 0.39/0.62          | ~ (v2_funct_1 @ X46)
% 0.39/0.62          | ((k2_tops_2 @ X45 @ X44 @ X46) = (k2_funct_1 @ X46))
% 0.39/0.62          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.39/0.62          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.39/0.62          | ~ (v1_funct_1 @ X46))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            = (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.62  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['36', '37'])).
% 0.39/0.62  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.62  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62          = (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.39/0.62  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62          = (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['34', '35', '40', '41', '46'])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.39/0.62          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.62           (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62          sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['27', '48'])).
% 0.39/0.62  thf(fc6_funct_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.39/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.39/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.39/0.62         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X16 : $i]:
% 0.39/0.62         ((v2_funct_1 @ (k2_funct_1 @ X16))
% 0.39/0.62          | ~ (v2_funct_1 @ X16)
% 0.39/0.62          | ~ (v1_funct_1 @ X16)
% 0.39/0.62          | ~ (v1_relat_1 @ X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X16 : $i]:
% 0.39/0.62         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 0.39/0.62          | ~ (v2_funct_1 @ X16)
% 0.39/0.62          | ~ (v1_funct_1 @ X16)
% 0.39/0.62          | ~ (v1_relat_1 @ X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X16 : $i]:
% 0.39/0.62         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.39/0.62          | ~ (v2_funct_1 @ X16)
% 0.39/0.62          | ~ (v1_funct_1 @ X16)
% 0.39/0.62          | ~ (v1_relat_1 @ X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      (![X19 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X19)
% 0.39/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X19)) = (X19))
% 0.39/0.62          | ~ (v1_funct_1 @ X19)
% 0.39/0.62          | ~ (v1_relat_1 @ X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.39/0.62  thf(t55_funct_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.62       ( ( v2_funct_1 @ A ) =>
% 0.39/0.62         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.39/0.62           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (![X17 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X17)
% 0.39/0.62          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 0.39/0.62          | ~ (v1_funct_1 @ X17)
% 0.39/0.62          | ~ (v1_relat_1 @ X17))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['53', '54'])).
% 0.39/0.62  thf('56', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.39/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['56'])).
% 0.39/0.62  thf('58', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['51', '57'])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.39/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['58'])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['50', '59'])).
% 0.39/0.62  thf('61', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['60'])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (![X16 : $i]:
% 0.39/0.62         ((v2_funct_1 @ (k2_funct_1 @ X16))
% 0.39/0.62          | ~ (v2_funct_1 @ X16)
% 0.39/0.62          | ~ (v1_funct_1 @ X16)
% 0.39/0.62          | ~ (v1_relat_1 @ X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf(t31_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.39/0.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.39/0.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.39/0.62           ( m1_subset_1 @
% 0.39/0.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.39/0.62  thf('64', plain,
% 0.39/0.62      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X34)
% 0.39/0.62          | ((k2_relset_1 @ X36 @ X35 @ X34) != (X35))
% 0.39/0.62          | (m1_subset_1 @ (k2_funct_1 @ X34) @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.39/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.39/0.62          | ~ (v1_funct_2 @ X34 @ X36 @ X35)
% 0.39/0.62          | ~ (v1_funct_1 @ X34))),
% 0.39/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62           (k1_zfmisc_1 @ 
% 0.39/0.62            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.39/0.62  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('67', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.62  thf('68', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.39/0.62  thf('71', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.39/0.62  thf('72', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.62         ((m1_subset_1 @ (k2_relset_1 @ X23 @ X24 @ X25) @ (k1_zfmisc_1 @ X24))
% 0.39/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      ((m1_subset_1 @ 
% 0.39/0.62        (k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62         (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.39/0.62  thf('74', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.39/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.62  thf('75', plain,
% 0.39/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.62         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.39/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.39/0.62  thf('77', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['73', '76'])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('79', plain,
% 0.39/0.62      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.39/0.62  thf(t4_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.62       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.39/0.62         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.39/0.62           ( m1_subset_1 @
% 0.39/0.62             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      (![X40 : $i, X41 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 0.39/0.62          | (m1_subset_1 @ X40 @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ X41)))
% 0.39/0.62          | ~ (v1_funct_1 @ X40)
% 0.39/0.62          | ~ (v1_relat_1 @ X40))),
% 0.39/0.62      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.39/0.62  thf('81', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62           (k1_zfmisc_1 @ 
% 0.39/0.62            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62             (u1_struct_0 @ sk_A)))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['79', '80'])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.39/0.62  thf(cc1_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( v1_relat_1 @ C ) ))).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.62         ((v1_relat_1 @ X20)
% 0.39/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.62  thf('84', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['82', '83'])).
% 0.39/0.62  thf('85', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf('86', plain,
% 0.39/0.62      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X34)
% 0.39/0.62          | ((k2_relset_1 @ X36 @ X35 @ X34) != (X35))
% 0.39/0.62          | (v1_funct_1 @ (k2_funct_1 @ X34))
% 0.39/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.39/0.62          | ~ (v1_funct_2 @ X34 @ X36 @ X35)
% 0.39/0.62          | ~ (v1_funct_1 @ X34))),
% 0.39/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.62  thf('87', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.62        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.62  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('89', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.62  thf('90', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('92', plain,
% 0.39/0.62      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 0.39/0.62  thf('93', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['92'])).
% 0.39/0.62  thf('94', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62          (u1_struct_0 @ sk_A))))),
% 0.39/0.62      inference('demod', [status(thm)], ['81', '84', '93'])).
% 0.39/0.62  thf('95', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('96', plain,
% 0.39/0.62      (![X17 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X17)
% 0.39/0.62          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 0.39/0.62          | ~ (v1_funct_1 @ X17)
% 0.39/0.62          | ~ (v1_relat_1 @ X17))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.62  thf('97', plain,
% 0.39/0.62      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.39/0.62  thf('98', plain,
% 0.39/0.62      (((r1_tarski @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['96', '97'])).
% 0.39/0.62  thf('99', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('100', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf(t35_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.39/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.62           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.39/0.62             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.39/0.62  thf('101', plain,
% 0.39/0.62      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.39/0.62         (((X37) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_funct_1 @ X38)
% 0.39/0.62          | ~ (v1_funct_2 @ X38 @ X39 @ X37)
% 0.39/0.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.39/0.62          | ((k5_relat_1 @ X38 @ (k2_funct_1 @ X38)) = (k6_partfun1 @ X39))
% 0.39/0.62          | ~ (v2_funct_1 @ X38)
% 0.39/0.62          | ((k2_relset_1 @ X39 @ X37 @ X38) != (X37)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.39/0.62  thf(redefinition_k6_partfun1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.39/0.62  thf('102', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.62  thf('103', plain,
% 0.39/0.62      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.39/0.62         (((X37) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_funct_1 @ X38)
% 0.39/0.62          | ~ (v1_funct_2 @ X38 @ X39 @ X37)
% 0.39/0.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.39/0.62          | ((k5_relat_1 @ X38 @ (k2_funct_1 @ X38)) = (k6_relat_1 @ X39))
% 0.39/0.62          | ~ (v2_funct_1 @ X38)
% 0.39/0.62          | ((k2_relset_1 @ X39 @ X37 @ X38) != (X37)))),
% 0.39/0.62      inference('demod', [status(thm)], ['101', '102'])).
% 0.39/0.62  thf('104', plain,
% 0.39/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62          != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.39/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['100', '103'])).
% 0.39/0.62  thf('105', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('107', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.62  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('109', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.39/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.39/0.62  thf('110', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.39/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.39/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['109'])).
% 0.39/0.62  thf(t58_funct_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.62       ( ( v2_funct_1 @ A ) =>
% 0.39/0.62         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.39/0.62             ( k1_relat_1 @ A ) ) & 
% 0.39/0.62           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.39/0.62             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.39/0.62  thf('111', plain,
% 0.39/0.62      (![X18 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X18)
% 0.39/0.62          | ((k2_relat_1 @ (k5_relat_1 @ X18 @ (k2_funct_1 @ X18)))
% 0.39/0.62              = (k1_relat_1 @ X18))
% 0.39/0.62          | ~ (v1_funct_1 @ X18)
% 0.39/0.62          | ~ (v1_relat_1 @ X18))),
% 0.39/0.62      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.39/0.62  thf('112', plain,
% 0.39/0.62      ((((k2_relat_1 @ (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62          = (k1_relat_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['110', '111'])).
% 0.39/0.62  thf(t71_relat_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.39/0.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.62  thf('113', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.62  thf('114', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('115', plain,
% 0.39/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.62         ((v1_relat_1 @ X20)
% 0.39/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.62  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.39/0.62  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('119', plain,
% 0.39/0.62      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['112', '113', '116', '117', '118'])).
% 0.39/0.62  thf('120', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['99', '119'])).
% 0.39/0.62  thf('121', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('122', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['120', '121'])).
% 0.39/0.62  thf('123', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['20', '22', '23'])).
% 0.39/0.62  thf(fc2_struct_0, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.62  thf('124', plain,
% 0.39/0.62      (![X43 : $i]:
% 0.39/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X43))
% 0.39/0.62          | ~ (l1_struct_0 @ X43)
% 0.39/0.62          | (v2_struct_0 @ X43))),
% 0.39/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.62  thf('125', plain,
% 0.39/0.62      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.39/0.62        | (v2_struct_0 @ sk_B)
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['123', '124'])).
% 0.39/0.62  thf('126', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('127', plain,
% 0.39/0.62      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['125', '126'])).
% 0.39/0.62  thf('128', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('129', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('clc', [status(thm)], ['127', '128'])).
% 0.39/0.62  thf('130', plain,
% 0.39/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.62        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['122', '129'])).
% 0.39/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.62  thf('131', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.62  thf('132', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['130', '131'])).
% 0.39/0.62  thf('133', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.39/0.62  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('136', plain,
% 0.39/0.62      ((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['98', '132', '133', '134', '135'])).
% 0.39/0.62  thf('137', plain,
% 0.39/0.62      (![X0 : $i, X2 : $i]:
% 0.39/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('138', plain,
% 0.39/0.62      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.39/0.62        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['136', '137'])).
% 0.39/0.62  thf('139', plain,
% 0.39/0.62      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.62        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['95', '138'])).
% 0.39/0.62  thf('140', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.62  thf('141', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('142', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.39/0.62  thf('143', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62          (k2_struct_0 @ sk_A))))),
% 0.39/0.62      inference('demod', [status(thm)], ['94', '142'])).
% 0.39/0.62  thf('144', plain,
% 0.39/0.62      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.39/0.62         (((k2_relset_1 @ X45 @ X44 @ X46) != (X44))
% 0.39/0.62          | ~ (v2_funct_1 @ X46)
% 0.39/0.62          | ((k2_tops_2 @ X45 @ X44 @ X46) = (k2_funct_1 @ X46))
% 0.39/0.62          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.39/0.62          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.39/0.62          | ~ (v1_funct_1 @ X46))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.62  thf('145', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62             (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))
% 0.39/0.62        | ((k2_tops_2 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62            (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C))
% 0.39/0.62            = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62            (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['143', '144'])).
% 0.39/0.62  thf('146', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['92'])).
% 0.39/0.62  thf('147', plain,
% 0.39/0.62      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.39/0.62  thf('148', plain,
% 0.39/0.62      (![X40 : $i, X41 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 0.39/0.62          | (v1_funct_2 @ X40 @ (k1_relat_1 @ X40) @ X41)
% 0.39/0.62          | ~ (v1_funct_1 @ X40)
% 0.39/0.62          | ~ (v1_relat_1 @ X40))),
% 0.39/0.62      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.39/0.62  thf('149', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['147', '148'])).
% 0.39/0.62  thf('150', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['82', '83'])).
% 0.39/0.62  thf('151', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['92'])).
% 0.39/0.62  thf('152', plain,
% 0.39/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.39/0.62  thf('153', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.39/0.62  thf('154', plain,
% 0.39/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['152', '153'])).
% 0.39/0.62  thf('155', plain,
% 0.39/0.62      (![X17 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X17)
% 0.39/0.62          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 0.39/0.62          | ~ (v1_funct_1 @ X17)
% 0.39/0.62          | ~ (v1_relat_1 @ X17))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.62  thf('156', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('157', plain,
% 0.39/0.62      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.39/0.62  thf('158', plain,
% 0.39/0.62      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup+', [status(thm)], ['156', '157'])).
% 0.39/0.62  thf('159', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('160', plain,
% 0.39/0.62      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['158', '159'])).
% 0.39/0.62  thf('161', plain,
% 0.39/0.62      (![X0 : $i, X2 : $i]:
% 0.39/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('162', plain,
% 0.39/0.62      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.62           (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.62        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['160', '161'])).
% 0.39/0.62  thf('163', plain,
% 0.39/0.62      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k1_relat_1 @ sk_C))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['155', '162'])).
% 0.39/0.62  thf('164', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['130', '131'])).
% 0.39/0.62  thf('165', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.62  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.39/0.62  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('169', plain,
% 0.39/0.62      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['163', '164', '165', '166', '167', '168'])).
% 0.39/0.62  thf('170', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.62  thf('171', plain,
% 0.39/0.62      (![X40 : $i, X41 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 0.39/0.62          | (m1_subset_1 @ X40 @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ X41)))
% 0.39/0.62          | ~ (v1_funct_1 @ X40)
% 0.39/0.62          | ~ (v1_relat_1 @ X40))),
% 0.39/0.62      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.39/0.62  thf('172', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | (m1_subset_1 @ X0 @ 
% 0.39/0.62             (k1_zfmisc_1 @ 
% 0.39/0.62              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['170', '171'])).
% 0.39/0.62  thf('173', plain,
% 0.39/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.62         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.39/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.62  thf('174', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.39/0.62              = (k2_relat_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['172', '173'])).
% 0.39/0.62  thf('175', plain,
% 0.39/0.62      ((((k2_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62          (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C))
% 0.39/0.62          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['169', '174'])).
% 0.39/0.62  thf('176', plain,
% 0.39/0.62      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['163', '164', '165', '166', '167', '168'])).
% 0.39/0.62  thf('177', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['82', '83'])).
% 0.39/0.62  thf('178', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['92'])).
% 0.39/0.62  thf('179', plain,
% 0.39/0.62      (((k2_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62         (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 0.39/0.62  thf('180', plain,
% 0.39/0.62      ((((k2_tops_2 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62          (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C))
% 0.39/0.62          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['145', '146', '154', '179'])).
% 0.39/0.62  thf('181', plain,
% 0.39/0.62      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_tops_2 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62            (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C))
% 0.39/0.62            = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['180'])).
% 0.39/0.62  thf('182', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ((k2_tops_2 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62            (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C))
% 0.39/0.62            = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['62', '181'])).
% 0.39/0.62  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.39/0.62  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('186', plain,
% 0.39/0.62      (((k2_tops_2 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62         (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C))
% 0.39/0.62         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 0.39/0.62  thf('187', plain,
% 0.39/0.62      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.62          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['61', '186'])).
% 0.39/0.62  thf('188', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf('189', plain,
% 0.39/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.62         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.39/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.62  thf('190', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_relat_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['188', '189'])).
% 0.39/0.62  thf('191', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.62  thf('192', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['190', '191'])).
% 0.39/0.62  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.39/0.62  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('195', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('196', plain,
% 0.39/0.62      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.62         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['187', '192', '193', '194', '195'])).
% 0.39/0.62  thf('197', plain,
% 0.39/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.39/0.62          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['49', '196'])).
% 0.39/0.62  thf('198', plain,
% 0.39/0.62      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.62           sk_C)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['0', '197'])).
% 0.39/0.62  thf('199', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('200', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('201', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('202', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_C @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup+', [status(thm)], ['200', '201'])).
% 0.39/0.62  thf('203', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('204', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('demod', [status(thm)], ['202', '203'])).
% 0.39/0.62  thf('205', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_C @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['199', '204'])).
% 0.39/0.62  thf('206', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('207', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.62      inference('demod', [status(thm)], ['205', '206'])).
% 0.39/0.62  thf('208', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf(reflexivity_r2_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.62         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.39/0.62  thf('209', plain,
% 0.39/0.62      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.39/0.62         ((r2_funct_2 @ X30 @ X31 @ X32 @ X32)
% 0.39/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.39/0.62          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.39/0.62          | ~ (v1_funct_1 @ X32)
% 0.39/0.62          | ~ (v1_funct_1 @ X33)
% 0.39/0.62          | ~ (v1_funct_2 @ X33 @ X30 @ X31)
% 0.39/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.39/0.62      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.39/0.62  thf('210', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X0 @ 
% 0.39/0.62             (k1_zfmisc_1 @ 
% 0.39/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.62          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.62             sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['208', '209'])).
% 0.39/0.62  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('212', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.62  thf('213', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X0 @ 
% 0.39/0.62             (k1_zfmisc_1 @ 
% 0.39/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.62             sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['210', '211', '212'])).
% 0.39/0.62  thf('214', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.39/0.62  thf('215', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.39/0.62  thf('216', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.39/0.62  thf('217', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X0 @ 
% 0.39/0.62             (k1_zfmisc_1 @ 
% 0.39/0.62              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.62          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.62             sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['213', '214', '215', '216'])).
% 0.39/0.62  thf('218', plain,
% 0.39/0.62      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['207', '217'])).
% 0.39/0.62  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('220', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('221', plain,
% 0.39/0.62      (![X42 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('222', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('223', plain,
% 0.39/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.62      inference('sup+', [status(thm)], ['221', '222'])).
% 0.39/0.62  thf('224', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('225', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['223', '224'])).
% 0.39/0.62  thf('226', plain,
% 0.39/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.63      inference('sup+', [status(thm)], ['220', '225'])).
% 0.39/0.63  thf('227', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('228', plain,
% 0.39/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.63      inference('demod', [status(thm)], ['226', '227'])).
% 0.39/0.63  thf('229', plain,
% 0.39/0.63      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.39/0.63      inference('demod', [status(thm)], ['218', '219', '228'])).
% 0.39/0.63  thf('230', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.63      inference('sup-', [status(thm)], ['114', '115'])).
% 0.39/0.63  thf('231', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('232', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('233', plain, ($false),
% 0.39/0.63      inference('demod', [status(thm)], ['198', '229', '230', '231', '232'])).
% 0.39/0.63  
% 0.39/0.63  % SZS output end Refutation
% 0.39/0.63  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
