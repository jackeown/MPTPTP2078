%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JESoTi5Fjm

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:15 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  286 (3353 expanded)
%              Number of leaves         :   46 ( 983 expanded)
%              Depth                    :   22
%              Number of atoms          : 2610 (72540 expanded)
%              Number of equality atoms :  143 (2033 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('37',plain,(
    ! [X37: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['35','42'])).

thf('44',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('47',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('62',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['35','42'])).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('72',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['12','61','69','70','71'])).

thf('73',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

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

thf('82',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X38 @ X40 )
       != X38 )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_tops_2 @ X39 @ X38 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('99',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('102',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('116',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('118',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84','97','103','104','118'])).

thf('120',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['72','120'])).

thf('122',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('124',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('125',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('127',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_relset_1 @ X19 @ X20 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('128',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['125','128'])).

thf('130',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('134',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X38 @ X40 )
       != X38 )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_tops_2 @ X39 @ X38 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('136',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

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

thf('138',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('142',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143','144'])).

thf('146',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('148',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('149',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X33 ) @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('152',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('155',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('159',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('160',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('162',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','156','157','162','163'])).

thf('165',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','164'])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('167',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('171',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('172',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('178',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X21 @ ( k3_relset_1 @ X21 @ X22 @ X23 ) )
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('179',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('181',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_relset_1 @ X19 @ X20 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('182',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('184',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('185',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','182','185'])).

thf('187',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('188',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','146','169','176','188'])).

thf('190',plain,
    ( ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('192',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('193',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('194',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t63_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) )).

thf('195',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( l1_struct_0 @ X41 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X41 ) @ X43 )
       != ( k2_struct_0 @ X41 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X41 ) @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['193','197'])).

thf('199',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['198','199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','201'])).

thf('203',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('204',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('205',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('206',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['202','203','204','205','206'])).

thf('208',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','207'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('211',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('212',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('213',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X38 @ X40 )
       != X38 )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_tops_2 @ X39 @ X38 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('214',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('217',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('220',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['214','215','216','217','218','219'])).

thf('221',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','220'])).

thf('222',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('223',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('228',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['208','209','210','225','226','227'])).

thf('229',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['190','229'])).

thf('231',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('232',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( r2_funct_2 @ X30 @ X31 @ X29 @ X32 )
      | ( X29 != X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('233',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_funct_2 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['231','233'])).

thf('235',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('236',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,(
    $false ),
    inference(demod,[status(thm)],['121','230','237'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JESoTi5Fjm
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 584 iterations in 0.151s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.37/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.61  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.37/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.61  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.37/0.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.37/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.61  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.37/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.61  thf(d3_struct_0, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf(t64_tops_2, conjecture,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_struct_0 @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.61                 ( m1_subset_1 @
% 0.37/0.61                   C @ 
% 0.37/0.61                   ( k1_zfmisc_1 @
% 0.37/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.61               ( ( ( ( k2_relset_1 @
% 0.37/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.61                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.61                   ( v2_funct_1 @ C ) ) =>
% 0.37/0.61                 ( r2_funct_2 @
% 0.37/0.61                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.37/0.61                   ( k2_tops_2 @
% 0.37/0.61                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.61                     ( k2_tops_2 @
% 0.37/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.37/0.61                   C ) ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]:
% 0.37/0.61        ( ( l1_struct_0 @ A ) =>
% 0.37/0.61          ( ![B:$i]:
% 0.37/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.61              ( ![C:$i]:
% 0.37/0.61                ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.61                    ( v1_funct_2 @
% 0.37/0.61                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.61                    ( m1_subset_1 @
% 0.37/0.61                      C @ 
% 0.37/0.61                      ( k1_zfmisc_1 @
% 0.37/0.61                        ( k2_zfmisc_1 @
% 0.37/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.61                  ( ( ( ( k2_relset_1 @
% 0.37/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.61                        ( k2_struct_0 @ B ) ) & 
% 0.37/0.61                      ( v2_funct_1 @ C ) ) =>
% 0.37/0.61                    ( r2_funct_2 @
% 0.37/0.61                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.37/0.61                      ( k2_tops_2 @
% 0.37/0.61                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.61                        ( k2_tops_2 @
% 0.37/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.37/0.61                      C ) ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.61          sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.61           sk_C)
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.61  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.61          sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.61           sk_C)
% 0.37/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '6'])).
% 0.37/0.61  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.61          sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.61           sk_C)
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['0', '9'])).
% 0.37/0.61  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.61          sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (((m1_subset_1 @ sk_C @ 
% 0.37/0.61         (k1_zfmisc_1 @ 
% 0.37/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.61  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.61         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.37/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('23', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.37/0.61      inference('demod', [status(thm)], ['18', '23'])).
% 0.37/0.61  thf(cc5_funct_2, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.61       ( ![C:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.37/0.61             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.37/0.61          | (v1_partfun1 @ X24 @ X25)
% 0.37/0.61          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.37/0.61          | ~ (v1_funct_1 @ X24)
% 0.37/0.61          | (v1_xboole_0 @ X26))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.37/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.37/0.61        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.61  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.37/0.61  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.61  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.37/0.61        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['26', '27', '34'])).
% 0.37/0.61  thf('36', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf(fc5_struct_0, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.61       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      (![X37 : $i]:
% 0.37/0.61         (~ (v1_xboole_0 @ (k2_struct_0 @ X37))
% 0.37/0.61          | ~ (l1_struct_0 @ X37)
% 0.37/0.61          | (v2_struct_0 @ X37))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.37/0.61        | (v2_struct_0 @ sk_B)
% 0.37/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.61  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.37/0.61  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('42', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('clc', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('43', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['35', '42'])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['13', '43'])).
% 0.37/0.61  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('46', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.61  thf(d4_partfun1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.37/0.61       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (![X27 : $i, X28 : $i]:
% 0.37/0.61         (~ (v1_partfun1 @ X28 @ X27)
% 0.37/0.61          | ((k1_relat_1 @ X28) = (X27))
% 0.37/0.61          | ~ (v4_relat_1 @ X28 @ X27)
% 0.37/0.61          | ~ (v1_relat_1 @ X28))),
% 0.37/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.61        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.37/0.61        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.61  thf('49', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(cc2_relat_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.61          | (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.61  thf('51', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ 
% 0.37/0.61           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.37/0.61        | (v1_relat_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.61  thf(fc6_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.61  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.61  thf('54', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('56', plain,
% 0.37/0.61      (((m1_subset_1 @ sk_C @ 
% 0.37/0.61         (k1_zfmisc_1 @ 
% 0.37/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['54', '55'])).
% 0.37/0.61  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('58', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf(cc2_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.61  thf('59', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.61         ((v4_relat_1 @ X6 @ X7)
% 0.37/0.61          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.61  thf('60', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.61  thf('61', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('62', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['35', '42'])).
% 0.37/0.61  thf('63', plain,
% 0.37/0.61      (![X27 : $i, X28 : $i]:
% 0.37/0.61         (~ (v1_partfun1 @ X28 @ X27)
% 0.37/0.61          | ((k1_relat_1 @ X28) = (X27))
% 0.37/0.61          | ~ (v4_relat_1 @ X28 @ X27)
% 0.37/0.61          | ~ (v1_relat_1 @ X28))),
% 0.37/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.37/0.61  thf('64', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.61        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.37/0.61        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.61  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.61  thf('66', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('67', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.61         ((v4_relat_1 @ X6 @ X7)
% 0.37/0.61          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.61  thf('68', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.61  thf('69', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.37/0.61  thf('70', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('72', plain,
% 0.37/0.61      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.61           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.37/0.61          sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['12', '61', '69', '70', '71'])).
% 0.37/0.61  thf('73', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('74', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf('75', plain,
% 0.37/0.61      (((m1_subset_1 @ sk_C @ 
% 0.37/0.61         (k1_zfmisc_1 @ 
% 0.37/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['73', '74'])).
% 0.37/0.61  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('77', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.61  thf('78', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('79', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.37/0.61      inference('demod', [status(thm)], ['77', '78'])).
% 0.37/0.61  thf('80', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('81', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.37/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.37/0.61  thf(d4_tops_2, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.37/0.61         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.37/0.61  thf('82', plain,
% 0.37/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.37/0.61         (((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 0.37/0.61          | ~ (v2_funct_1 @ X40)
% 0.37/0.61          | ((k2_tops_2 @ X39 @ X38 @ X40) = (k2_funct_1 @ X40))
% 0.37/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.37/0.61          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.37/0.61          | ~ (v1_funct_1 @ X40))),
% 0.37/0.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.37/0.61  thf('83', plain,
% 0.37/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.37/0.61            = (k2_funct_1 @ sk_C))
% 0.37/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.61        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.37/0.61            != (k2_relat_1 @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['81', '82'])).
% 0.37/0.61  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('85', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('86', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('87', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('88', plain,
% 0.37/0.61      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['86', '87'])).
% 0.37/0.61  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('90', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['88', '89'])).
% 0.37/0.61  thf('91', plain,
% 0.37/0.61      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['85', '90'])).
% 0.37/0.61  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('93', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['91', '92'])).
% 0.37/0.61  thf('94', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('95', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['93', '94'])).
% 0.37/0.61  thf('96', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('97', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['95', '96'])).
% 0.37/0.61  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(d9_funct_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.37/0.61  thf('99', plain,
% 0.37/0.61      (![X4 : $i]:
% 0.37/0.61         (~ (v2_funct_1 @ X4)
% 0.37/0.61          | ((k2_funct_1 @ X4) = (k4_relat_1 @ X4))
% 0.37/0.61          | ~ (v1_funct_1 @ X4)
% 0.37/0.61          | ~ (v1_relat_1 @ X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.37/0.61  thf('100', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.61        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.37/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['98', '99'])).
% 0.37/0.61  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.61  thf('102', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('103', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.37/0.61  thf('104', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('105', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('106', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('107', plain,
% 0.37/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('108', plain,
% 0.37/0.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61          = (k2_struct_0 @ sk_B))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['106', '107'])).
% 0.37/0.61  thf('109', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('110', plain,
% 0.37/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['108', '109'])).
% 0.37/0.61  thf('111', plain,
% 0.37/0.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61          = (k2_struct_0 @ sk_B))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['105', '110'])).
% 0.37/0.61  thf('112', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('113', plain,
% 0.37/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['111', '112'])).
% 0.37/0.61  thf('114', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('115', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('116', plain,
% 0.37/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.37/0.61         = (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.37/0.61  thf('117', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('118', plain,
% 0.37/0.61      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.37/0.61         = (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['116', '117'])).
% 0.37/0.61  thf('119', plain,
% 0.37/0.61      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.37/0.61          = (k4_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['83', '84', '97', '103', '104', '118'])).
% 0.37/0.61  thf('120', plain,
% 0.37/0.61      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.37/0.61         = (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('simplify', [status(thm)], ['119'])).
% 0.37/0.61  thf('121', plain,
% 0.37/0.61      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.61           (k4_relat_1 @ sk_C)) @ 
% 0.37/0.61          sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['72', '120'])).
% 0.37/0.61  thf('122', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('123', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(dt_k3_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( m1_subset_1 @
% 0.37/0.61         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.37/0.61         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.37/0.61  thf('124', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k3_relset_1 @ X9 @ X10 @ X11) @ 
% 0.37/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 0.37/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.37/0.61  thf('125', plain,
% 0.37/0.61      ((m1_subset_1 @ 
% 0.37/0.61        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['123', '124'])).
% 0.37/0.61  thf('126', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k3_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.37/0.61  thf('127', plain,
% 0.37/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.61         (((k3_relset_1 @ X19 @ X20 @ X18) = (k4_relat_1 @ X18))
% 0.37/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.37/0.61  thf('128', plain,
% 0.37/0.61      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['126', '127'])).
% 0.37/0.61  thf('129', plain,
% 0.37/0.61      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['125', '128'])).
% 0.37/0.61  thf('130', plain,
% 0.37/0.61      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.37/0.61         (k1_zfmisc_1 @ 
% 0.37/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['122', '129'])).
% 0.37/0.61  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('132', plain,
% 0.37/0.61      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['130', '131'])).
% 0.37/0.61  thf('133', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('134', plain,
% 0.37/0.61      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.37/0.61      inference('demod', [status(thm)], ['132', '133'])).
% 0.37/0.61  thf('135', plain,
% 0.37/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.37/0.61         (((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 0.37/0.61          | ~ (v2_funct_1 @ X40)
% 0.37/0.61          | ((k2_tops_2 @ X39 @ X38 @ X40) = (k2_funct_1 @ X40))
% 0.37/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.37/0.61          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.37/0.61          | ~ (v1_funct_1 @ X40))),
% 0.37/0.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.37/0.61  thf('136', plain,
% 0.37/0.61      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.37/0.61        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61             (k1_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.61            (k4_relat_1 @ sk_C)) = (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 0.37/0.61        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.61            (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['134', '135'])).
% 0.37/0.61  thf('137', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.37/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.37/0.61  thf(t31_funct_2, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.37/0.61         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.37/0.61           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.37/0.61           ( m1_subset_1 @
% 0.37/0.61             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.37/0.61  thf('138', plain,
% 0.37/0.61      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.37/0.61         (~ (v2_funct_1 @ X33)
% 0.37/0.61          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 0.37/0.61          | (v1_funct_1 @ (k2_funct_1 @ X33))
% 0.37/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.37/0.61          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 0.37/0.61          | ~ (v1_funct_1 @ X33))),
% 0.37/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.37/0.61  thf('139', plain,
% 0.37/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.37/0.61        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.61        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.37/0.61            != (k2_relat_1 @ sk_C))
% 0.37/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['137', '138'])).
% 0.37/0.61  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('141', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['95', '96'])).
% 0.37/0.61  thf('142', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.37/0.61  thf('143', plain,
% 0.37/0.61      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.37/0.61         = (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['116', '117'])).
% 0.37/0.61  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('145', plain,
% 0.37/0.61      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)],
% 0.37/0.61                ['139', '140', '141', '142', '143', '144'])).
% 0.37/0.61  thf('146', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('simplify', [status(thm)], ['145'])).
% 0.37/0.61  thf('147', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('148', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf('149', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('150', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['148', '149'])).
% 0.37/0.61  thf('151', plain,
% 0.37/0.61      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.37/0.61         (~ (v2_funct_1 @ X33)
% 0.37/0.61          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 0.37/0.61          | (v1_funct_2 @ (k2_funct_1 @ X33) @ X34 @ X35)
% 0.37/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.37/0.61          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 0.37/0.61          | ~ (v1_funct_1 @ X33))),
% 0.37/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.37/0.61  thf('152', plain,
% 0.37/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.37/0.61        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61           (k1_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61            != (u1_struct_0 @ sk_B))
% 0.37/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['150', '151'])).
% 0.37/0.61  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('154', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['88', '89'])).
% 0.37/0.61  thf('155', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('156', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['154', '155'])).
% 0.37/0.61  thf('157', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.37/0.61  thf('158', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf('159', plain,
% 0.37/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.61         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.37/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.61  thf('160', plain,
% 0.37/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['158', '159'])).
% 0.37/0.61  thf('161', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('162', plain,
% 0.37/0.61      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['160', '161'])).
% 0.37/0.61  thf('163', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('164', plain,
% 0.37/0.61      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61         (k1_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.37/0.61      inference('demod', [status(thm)],
% 0.37/0.61                ['152', '153', '156', '157', '162', '163'])).
% 0.37/0.61  thf('165', plain,
% 0.37/0.61      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_B)
% 0.37/0.61        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61           (k1_relat_1 @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['147', '164'])).
% 0.37/0.61  thf('166', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('167', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('168', plain,
% 0.37/0.61      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.37/0.61        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61           (k1_relat_1 @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['165', '166', '167'])).
% 0.37/0.61  thf('169', plain,
% 0.37/0.61      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.61        (k1_relat_1 @ sk_C))),
% 0.37/0.61      inference('simplify', [status(thm)], ['168'])).
% 0.37/0.61  thf('170', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.37/0.61  thf(t65_funct_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.37/0.61  thf('171', plain,
% 0.37/0.61      (![X5 : $i]:
% 0.37/0.61         (~ (v2_funct_1 @ X5)
% 0.37/0.61          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.37/0.61          | ~ (v1_funct_1 @ X5)
% 0.37/0.61          | ~ (v1_relat_1 @ X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.37/0.61  thf('172', plain,
% 0.37/0.61      ((((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.61      inference('sup+', [status(thm)], ['170', '171'])).
% 0.37/0.61  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.61  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('175', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('176', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 0.37/0.61  thf('177', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf(t24_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.37/0.61           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.37/0.61         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.37/0.61           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.61  thf('178', plain,
% 0.37/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.61         (((k2_relset_1 @ X22 @ X21 @ (k3_relset_1 @ X21 @ X22 @ X23))
% 0.37/0.61            = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.37/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.37/0.61      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.37/0.61  thf('179', plain,
% 0.37/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.61         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.61         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['177', '178'])).
% 0.37/0.61  thf('180', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf('181', plain,
% 0.37/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.61         (((k3_relset_1 @ X19 @ X20 @ X18) = (k4_relat_1 @ X18))
% 0.37/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.37/0.61  thf('182', plain,
% 0.37/0.61      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['180', '181'])).
% 0.37/0.61  thf('183', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.61  thf('184', plain,
% 0.37/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.61         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.37/0.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.61  thf('185', plain,
% 0.37/0.61      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k1_relat_1 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['183', '184'])).
% 0.37/0.61  thf('186', plain,
% 0.37/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.61         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['179', '182', '185'])).
% 0.37/0.61  thf('187', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.37/0.61  thf('188', plain,
% 0.37/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.61         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['186', '187'])).
% 0.37/0.61  thf('189', plain,
% 0.37/0.61      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.61          (k4_relat_1 @ sk_C)) = (sk_C))
% 0.37/0.61        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.37/0.61        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['136', '146', '169', '176', '188'])).
% 0.37/0.61  thf('190', plain,
% 0.37/0.61      ((~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.61            (k4_relat_1 @ sk_C)) = (sk_C)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['189'])).
% 0.37/0.61  thf('191', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.37/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.37/0.61  thf('192', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.37/0.61  thf('193', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('194', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf(t63_tops_2, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_struct_0 @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( l1_struct_0 @ B ) =>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.61                 ( m1_subset_1 @
% 0.37/0.61                   C @ 
% 0.37/0.61                   ( k1_zfmisc_1 @
% 0.37/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.61               ( ( ( ( k2_relset_1 @
% 0.37/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.61                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.61                   ( v2_funct_1 @ C ) ) =>
% 0.37/0.61                 ( v2_funct_1 @
% 0.37/0.61                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.37/0.61  thf('195', plain,
% 0.37/0.61      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.37/0.61         (~ (l1_struct_0 @ X41)
% 0.37/0.61          | ((k2_relset_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X41) @ X43)
% 0.37/0.61              != (k2_struct_0 @ X41))
% 0.37/0.61          | ~ (v2_funct_1 @ X43)
% 0.37/0.61          | (v2_funct_1 @ 
% 0.37/0.61             (k2_tops_2 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X41) @ X43))
% 0.37/0.61          | ~ (m1_subset_1 @ X43 @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X41))))
% 0.37/0.61          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X41))
% 0.37/0.61          | ~ (v1_funct_1 @ X43)
% 0.37/0.61          | ~ (l1_struct_0 @ X42))),
% 0.37/0.61      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.37/0.61  thf('196', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X2 @ 
% 0.37/0.61             (k1_zfmisc_1 @ 
% 0.37/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X1)
% 0.37/0.61          | ~ (v1_funct_1 @ X2)
% 0.37/0.61          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.37/0.61          | (v2_funct_1 @ 
% 0.37/0.61             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.37/0.61          | ~ (v2_funct_1 @ X2)
% 0.37/0.61          | ((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.37/0.61              != (k2_struct_0 @ X0))
% 0.37/0.61          | ~ (l1_struct_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['194', '195'])).
% 0.37/0.61  thf('197', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.37/0.61            != (k2_struct_0 @ X0))
% 0.37/0.61          | ~ (v2_funct_1 @ X2)
% 0.37/0.61          | (v2_funct_1 @ 
% 0.37/0.61             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.37/0.61          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.37/0.61          | ~ (v1_funct_1 @ X2)
% 0.37/0.61          | ~ (l1_struct_0 @ X1)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X2 @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))))),
% 0.37/0.61      inference('simplify', [status(thm)], ['196'])).
% 0.37/0.61  thf('198', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.37/0.61             (k1_zfmisc_1 @ 
% 0.37/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.37/0.61          | ~ (l1_struct_0 @ sk_B)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X1)
% 0.37/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.37/0.61          | (v2_funct_1 @ 
% 0.37/0.61             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.37/0.61          | ~ (v2_funct_1 @ X1)
% 0.37/0.61          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.37/0.61              != (k2_struct_0 @ sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['193', '197'])).
% 0.37/0.61  thf('199', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('200', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('201', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.37/0.61             (k1_zfmisc_1 @ 
% 0.37/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X1)
% 0.37/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.37/0.61          | (v2_funct_1 @ 
% 0.37/0.61             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.37/0.61          | ~ (v2_funct_1 @ X1)
% 0.37/0.61          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.37/0.61              != (k2_relat_1 @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['198', '199', '200'])).
% 0.37/0.61  thf('202', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X0 @ 
% 0.37/0.61             (k1_zfmisc_1 @ 
% 0.37/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.37/0.61          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0)
% 0.37/0.61              != (k2_relat_1 @ sk_C))
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | (v2_funct_1 @ 
% 0.37/0.61             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0))
% 0.37/0.61          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['192', '201'])).
% 0.37/0.61  thf('203', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.37/0.61  thf('204', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.37/0.61  thf('205', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.37/0.61  thf('206', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('207', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X0 @ 
% 0.37/0.61             (k1_zfmisc_1 @ 
% 0.37/0.61              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.37/0.61          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0)
% 0.37/0.61              != (k2_relat_1 @ sk_C))
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | (v2_funct_1 @ 
% 0.37/0.61             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0))
% 0.37/0.61          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.37/0.61          | ~ (v1_funct_1 @ X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['202', '203', '204', '205', '206'])).
% 0.37/0.61  thf('208', plain,
% 0.37/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.37/0.61        | (v2_funct_1 @ 
% 0.37/0.61           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.61        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61            != (k2_relat_1 @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['191', '207'])).
% 0.37/0.61  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('210', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['154', '155'])).
% 0.37/0.61  thf('211', plain,
% 0.37/0.61      (![X36 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('212', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['148', '149'])).
% 0.37/0.61  thf('213', plain,
% 0.37/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.37/0.61         (((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 0.37/0.61          | ~ (v2_funct_1 @ X40)
% 0.37/0.61          | ((k2_tops_2 @ X39 @ X38 @ X40) = (k2_funct_1 @ X40))
% 0.37/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.37/0.61          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.37/0.61          | ~ (v1_funct_1 @ X40))),
% 0.37/0.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.37/0.61  thf('214', plain,
% 0.37/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.37/0.61        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61            = (k2_funct_1 @ sk_C))
% 0.37/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.61        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61            != (u1_struct_0 @ sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['212', '213'])).
% 0.37/0.61  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('216', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['154', '155'])).
% 0.37/0.61  thf('217', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.37/0.61  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('219', plain,
% 0.37/0.61      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['160', '161'])).
% 0.37/0.61  thf('220', plain,
% 0.37/0.61      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61          = (k4_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.37/0.61      inference('demod', [status(thm)],
% 0.37/0.61                ['214', '215', '216', '217', '218', '219'])).
% 0.37/0.61  thf('221', plain,
% 0.37/0.61      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_B)
% 0.37/0.61        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61            = (k4_relat_1 @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['211', '220'])).
% 0.37/0.61  thf('222', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('223', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('224', plain,
% 0.37/0.61      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61            = (k4_relat_1 @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['221', '222', '223'])).
% 0.37/0.61  thf('225', plain,
% 0.37/0.61      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('simplify', [status(thm)], ['224'])).
% 0.37/0.61  thf('226', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('227', plain,
% 0.37/0.61      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.61         = (k2_relat_1 @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['160', '161'])).
% 0.37/0.61  thf('228', plain,
% 0.37/0.61      (((v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.37/0.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)],
% 0.37/0.61                ['208', '209', '210', '225', '226', '227'])).
% 0.37/0.61  thf('229', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.37/0.61      inference('simplify', [status(thm)], ['228'])).
% 0.37/0.61  thf('230', plain,
% 0.37/0.61      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.61         (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['190', '229'])).
% 0.37/0.61  thf('231', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['148', '149'])).
% 0.37/0.61  thf(redefinition_r2_funct_2, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.61         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.37/0.61  thf('232', plain,
% 0.37/0.61      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.37/0.61          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.37/0.61          | ~ (v1_funct_1 @ X29)
% 0.37/0.61          | ~ (v1_funct_1 @ X32)
% 0.37/0.61          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.37/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.37/0.61          | (r2_funct_2 @ X30 @ X31 @ X29 @ X32)
% 0.37/0.61          | ((X29) != (X32)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.37/0.61  thf('233', plain,
% 0.37/0.61      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.61         ((r2_funct_2 @ X30 @ X31 @ X32 @ X32)
% 0.37/0.61          | ~ (v1_funct_1 @ X32)
% 0.37/0.61          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.37/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.37/0.61      inference('simplify', [status(thm)], ['232'])).
% 0.37/0.61  thf('234', plain,
% 0.37/0.61      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.37/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.61        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.37/0.61           sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['231', '233'])).
% 0.37/0.61  thf('235', plain,
% 0.37/0.61      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['154', '155'])).
% 0.37/0.61  thf('236', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('237', plain,
% 0.37/0.61      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['234', '235', '236'])).
% 0.37/0.61  thf('238', plain, ($false),
% 0.37/0.61      inference('demod', [status(thm)], ['121', '230', '237'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
