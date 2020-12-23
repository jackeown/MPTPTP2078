%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WzVf1Rz5eq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:57 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  335 (9694 expanded)
%              Number of leaves         :   48 (2788 expanded)
%              Depth                    :   33
%              Number of atoms          : 2935 (239427 expanded)
%              Number of equality atoms :  177 (12016 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
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
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

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
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','38'])).

thf('40',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','53'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X34 @ X35 @ X36 ) @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','64'])).

thf('66',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','53'])).

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

thf('68',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X31 @ X33 )
       != X31 )
      | ~ ( v2_funct_1 @ X33 )
      | ( ( k2_tops_2 @ X32 @ X31 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('75',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('77',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','77'])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','83'])).

thf('85',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86','87'])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('89',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','53'])).

thf('93',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['82'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('100',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('101',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('107',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('108',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('109',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('110',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','111'])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['104','115'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('118',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','118'])).

thf('120',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['91','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('122',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','123'])).

thf('125',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('126',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('127',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','53'])).

thf('130',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X34 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('131',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('134',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['128','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('137',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('141',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X31 @ X33 )
       != X31 )
      | ~ ( v2_funct_1 @ X33 )
      | ( ( k2_tops_2 @ X32 @ X31 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('149',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('152',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('153',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('162',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('163',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['161','166'])).

thf('168',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('172',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('174',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','150','159','160','174'])).

thf('176',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['138','176'])).

thf('178',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','83'])).

thf('179',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','177','178'])).

thf('180',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('182',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['179','182'])).

thf('184',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('185',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('188',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('190',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('192',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('193',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('194',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('195',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('196',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('197',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('199',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('202',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
       != X27 )
      | ( v1_partfun1 @ X28 @ X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('203',plain,(
    ! [X28: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v4_relat_1 @ X28 @ ( k1_relat_1 @ X28 ) )
      | ( v1_partfun1 @ X28 @ ( k1_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['201','203'])).

thf('205',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['200','204'])).

thf('206',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('207',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('210',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','206','207','208','209'])).

thf('211',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['194','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['211','212','213','214'])).

thf('216',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('217',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('219',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('220',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['185','190','193','220'])).

thf('222',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('223',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('224',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['224'])).

thf('226',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['223','225'])).

thf('227',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['222','228'])).

thf('230',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('233',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('234',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['231','232','233'])).

thf('235',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['221','234'])).

thf('236',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('237',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','38'])).

thf('238',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('239',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('241',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('243',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['239','240','243'])).

thf('245',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['175'])).

thf('246',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['235','236','244','245'])).

thf('247',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('248',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('249',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('250',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('252',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('255',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['175'])).

thf('257',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('258',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('259',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('260',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['224'])).

thf('261',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['261','262'])).

thf('264',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['258','263'])).

thf('265',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['257','266'])).

thf('268',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('269',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['267','268'])).

thf('270',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['239','240','243'])).

thf('271',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['239','240','243'])).

thf('272',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('273',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['269','270','271','272'])).

thf('274',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['256','273'])).

thf('275',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['255','274'])).

thf('276',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['247','275'])).

thf('277',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('278',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['276','277','278','279'])).

thf('281',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['280'])).

thf('282',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['224'])).

thf('283',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['281','282'])).

thf('284',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['246','283'])).

thf('285',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','284'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WzVf1Rz5eq
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.07/1.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.29  % Solved by: fo/fo7.sh
% 1.07/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.29  % done 653 iterations in 0.854s
% 1.07/1.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.29  % SZS output start Refutation
% 1.07/1.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.29  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.07/1.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.29  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.07/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.29  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.07/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.29  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.29  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.07/1.29  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.07/1.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.07/1.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.29  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.07/1.29  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.07/1.29  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.07/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.29  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.07/1.29  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.07/1.29  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.07/1.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.07/1.29  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.07/1.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.29  thf(d3_struct_0, axiom,
% 1.07/1.29    (![A:$i]:
% 1.07/1.29     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.07/1.29  thf('0', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('1', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf(t62_tops_2, conjecture,
% 1.07/1.29    (![A:$i]:
% 1.07/1.29     ( ( l1_struct_0 @ A ) =>
% 1.07/1.29       ( ![B:$i]:
% 1.07/1.29         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.07/1.29           ( ![C:$i]:
% 1.07/1.29             ( ( ( v1_funct_1 @ C ) & 
% 1.07/1.29                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.29                 ( m1_subset_1 @
% 1.07/1.29                   C @ 
% 1.07/1.29                   ( k1_zfmisc_1 @
% 1.07/1.29                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.29               ( ( ( ( k2_relset_1 @
% 1.07/1.29                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.07/1.29                     ( k2_struct_0 @ B ) ) & 
% 1.07/1.29                   ( v2_funct_1 @ C ) ) =>
% 1.07/1.29                 ( ( ( k1_relset_1 @
% 1.07/1.29                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.07/1.29                       ( k2_tops_2 @
% 1.07/1.29                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.07/1.29                     ( k2_struct_0 @ B ) ) & 
% 1.07/1.29                   ( ( k2_relset_1 @
% 1.07/1.29                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.07/1.29                       ( k2_tops_2 @
% 1.07/1.29                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.07/1.29                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.07/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.29    (~( ![A:$i]:
% 1.07/1.29        ( ( l1_struct_0 @ A ) =>
% 1.07/1.29          ( ![B:$i]:
% 1.07/1.29            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.07/1.29              ( ![C:$i]:
% 1.07/1.29                ( ( ( v1_funct_1 @ C ) & 
% 1.07/1.29                    ( v1_funct_2 @
% 1.07/1.29                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.07/1.29                    ( m1_subset_1 @
% 1.07/1.29                      C @ 
% 1.07/1.29                      ( k1_zfmisc_1 @
% 1.07/1.29                        ( k2_zfmisc_1 @
% 1.07/1.29                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.07/1.29                  ( ( ( ( k2_relset_1 @
% 1.07/1.29                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.07/1.29                        ( k2_struct_0 @ B ) ) & 
% 1.07/1.29                      ( v2_funct_1 @ C ) ) =>
% 1.07/1.29                    ( ( ( k1_relset_1 @
% 1.07/1.29                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.07/1.29                          ( k2_tops_2 @
% 1.07/1.29                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.07/1.29                        ( k2_struct_0 @ B ) ) & 
% 1.07/1.29                      ( ( k2_relset_1 @
% 1.07/1.29                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.07/1.29                          ( k2_tops_2 @
% 1.07/1.29                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.07/1.29                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.07/1.29    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.07/1.29  thf('2', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('3', plain,
% 1.07/1.29      (((m1_subset_1 @ sk_C @ 
% 1.07/1.29         (k1_zfmisc_1 @ 
% 1.07/1.29          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_A))),
% 1.07/1.29      inference('sup+', [status(thm)], ['1', '2'])).
% 1.07/1.29  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('5', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['3', '4'])).
% 1.07/1.29  thf('6', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('7', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('8', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('9', plain,
% 1.07/1.29      (((m1_subset_1 @ sk_C @ 
% 1.07/1.29         (k1_zfmisc_1 @ 
% 1.07/1.29          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['7', '8'])).
% 1.07/1.29  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('11', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['9', '10'])).
% 1.07/1.29  thf('12', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf(redefinition_k2_relset_1, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.29       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.07/1.29  thf('13', plain,
% 1.07/1.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.29         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.07/1.29          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.07/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.29  thf('14', plain,
% 1.07/1.29      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29         = (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('sup-', [status(thm)], ['12', '13'])).
% 1.07/1.29  thf('15', plain,
% 1.07/1.29      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29         = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('17', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['11', '16'])).
% 1.07/1.29  thf(cc5_funct_2, axiom,
% 1.07/1.29    (![A:$i,B:$i]:
% 1.07/1.29     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.07/1.29       ( ![C:$i]:
% 1.07/1.29         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.29           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.07/1.29             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.07/1.29  thf('18', plain,
% 1.07/1.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.07/1.29         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.07/1.29          | (v1_partfun1 @ X16 @ X17)
% 1.07/1.29          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 1.07/1.29          | ~ (v1_funct_1 @ X16)
% 1.07/1.29          | (v1_xboole_0 @ X18))),
% 1.07/1.29      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.07/1.29  thf('19', plain,
% 1.07/1.29      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.07/1.29        | ~ (v1_funct_1 @ sk_C)
% 1.07/1.29        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.07/1.29        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['17', '18'])).
% 1.07/1.29  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('21', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('22', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('23', plain,
% 1.07/1.29      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['21', '22'])).
% 1.07/1.29  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('25', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.29  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('27', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['25', '26'])).
% 1.07/1.29  thf('28', plain,
% 1.07/1.29      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.07/1.29        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.07/1.29      inference('demod', [status(thm)], ['19', '20', '27'])).
% 1.07/1.29  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('30', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf(fc2_struct_0, axiom,
% 1.07/1.29    (![A:$i]:
% 1.07/1.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.07/1.29       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.07/1.29  thf('31', plain,
% 1.07/1.29      (![X30 : $i]:
% 1.07/1.29         (~ (v1_xboole_0 @ (u1_struct_0 @ X30))
% 1.07/1.29          | ~ (l1_struct_0 @ X30)
% 1.07/1.29          | (v2_struct_0 @ X30))),
% 1.07/1.29      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.07/1.29  thf('32', plain,
% 1.07/1.29      (![X0 : $i]:
% 1.07/1.29         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.07/1.29          | ~ (l1_struct_0 @ X0)
% 1.07/1.29          | (v2_struct_0 @ X0)
% 1.07/1.29          | ~ (l1_struct_0 @ X0))),
% 1.07/1.29      inference('sup-', [status(thm)], ['30', '31'])).
% 1.07/1.29  thf('33', plain,
% 1.07/1.29      (![X0 : $i]:
% 1.07/1.29         ((v2_struct_0 @ X0)
% 1.07/1.29          | ~ (l1_struct_0 @ X0)
% 1.07/1.29          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.07/1.29      inference('simplify', [status(thm)], ['32'])).
% 1.07/1.29  thf('34', plain,
% 1.07/1.29      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B)
% 1.07/1.29        | (v2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup-', [status(thm)], ['29', '33'])).
% 1.07/1.29  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('36', plain,
% 1.07/1.29      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['34', '35'])).
% 1.07/1.29  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('38', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('clc', [status(thm)], ['36', '37'])).
% 1.07/1.29  thf('39', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.07/1.29      inference('clc', [status(thm)], ['28', '38'])).
% 1.07/1.29  thf('40', plain,
% 1.07/1.29      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.07/1.29      inference('sup+', [status(thm)], ['6', '39'])).
% 1.07/1.29  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('42', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['40', '41'])).
% 1.07/1.29  thf(d4_partfun1, axiom,
% 1.07/1.29    (![A:$i,B:$i]:
% 1.07/1.29     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.07/1.29       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.07/1.29  thf('43', plain,
% 1.07/1.29      (![X27 : $i, X28 : $i]:
% 1.07/1.29         (~ (v1_partfun1 @ X28 @ X27)
% 1.07/1.29          | ((k1_relat_1 @ X28) = (X27))
% 1.07/1.29          | ~ (v4_relat_1 @ X28 @ X27)
% 1.07/1.29          | ~ (v1_relat_1 @ X28))),
% 1.07/1.29      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.07/1.29  thf('44', plain,
% 1.07/1.29      ((~ (v1_relat_1 @ sk_C)
% 1.07/1.29        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.07/1.29        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['42', '43'])).
% 1.07/1.29  thf('45', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf(cc2_relat_1, axiom,
% 1.07/1.29    (![A:$i]:
% 1.07/1.29     ( ( v1_relat_1 @ A ) =>
% 1.07/1.29       ( ![B:$i]:
% 1.07/1.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.07/1.29  thf('46', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i]:
% 1.07/1.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.29          | (v1_relat_1 @ X0)
% 1.07/1.29          | ~ (v1_relat_1 @ X1))),
% 1.07/1.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.29  thf('47', plain,
% 1.07/1.29      ((~ (v1_relat_1 @ 
% 1.07/1.29           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.07/1.29        | (v1_relat_1 @ sk_C))),
% 1.07/1.29      inference('sup-', [status(thm)], ['45', '46'])).
% 1.07/1.29  thf(fc6_relat_1, axiom,
% 1.07/1.29    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.07/1.29  thf('48', plain,
% 1.07/1.29      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.07/1.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.29  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.29      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.29  thf('50', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['3', '4'])).
% 1.07/1.29  thf(cc2_relset_1, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.29       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.07/1.29  thf('51', plain,
% 1.07/1.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.07/1.29         ((v4_relat_1 @ X7 @ X8)
% 1.07/1.29          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.07/1.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.29  thf('52', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.29  thf('53', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('54', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['5', '53'])).
% 1.07/1.29  thf(dt_k2_tops_2, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.29       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 1.07/1.29         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 1.07/1.29         ( m1_subset_1 @
% 1.07/1.29           ( k2_tops_2 @ A @ B @ C ) @ 
% 1.07/1.29           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 1.07/1.29  thf('55', plain,
% 1.07/1.29      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.29         ((v1_funct_2 @ (k2_tops_2 @ X34 @ X35 @ X36) @ X35 @ X34)
% 1.07/1.29          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.07/1.29          | ~ (v1_funct_2 @ X36 @ X34 @ X35)
% 1.07/1.29          | ~ (v1_funct_1 @ X36))),
% 1.07/1.29      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.07/1.29  thf('56', plain,
% 1.07/1.29      ((~ (v1_funct_1 @ sk_C)
% 1.07/1.29        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.29        | (v1_funct_2 @ 
% 1.07/1.29           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.07/1.29           (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['54', '55'])).
% 1.07/1.29  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('58', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('59', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('60', plain,
% 1.07/1.29      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_A))),
% 1.07/1.29      inference('sup+', [status(thm)], ['58', '59'])).
% 1.07/1.29  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('62', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['60', '61'])).
% 1.07/1.29  thf('63', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('64', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['62', '63'])).
% 1.07/1.29  thf('65', plain,
% 1.07/1.29      ((v1_funct_2 @ 
% 1.07/1.29        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.07/1.29        (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['56', '57', '64'])).
% 1.07/1.29  thf('66', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('67', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['5', '53'])).
% 1.07/1.29  thf(d4_tops_2, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.29       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.07/1.29         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.07/1.29  thf('68', plain,
% 1.07/1.29      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.07/1.29         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 1.07/1.29          | ~ (v2_funct_1 @ X33)
% 1.07/1.29          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 1.07/1.29          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.07/1.29          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 1.07/1.29          | ~ (v1_funct_1 @ X33))),
% 1.07/1.29      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.07/1.29  thf('69', plain,
% 1.07/1.29      ((~ (v1_funct_1 @ sk_C)
% 1.07/1.29        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.29        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29            = (k2_funct_1 @ sk_C))
% 1.07/1.29        | ~ (v2_funct_1 @ sk_C)
% 1.07/1.29        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29            != (u1_struct_0 @ sk_B)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['67', '68'])).
% 1.07/1.29  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('71', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['62', '63'])).
% 1.07/1.29  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('73', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['3', '4'])).
% 1.07/1.29  thf('74', plain,
% 1.07/1.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.29         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.07/1.29          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.07/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.29  thf('75', plain,
% 1.07/1.29      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29         = (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('sup-', [status(thm)], ['73', '74'])).
% 1.07/1.29  thf('76', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('77', plain,
% 1.07/1.29      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29         = (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['75', '76'])).
% 1.07/1.29  thf('78', plain,
% 1.07/1.29      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29          = (k2_funct_1 @ sk_C))
% 1.07/1.29        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.07/1.29      inference('demod', [status(thm)], ['69', '70', '71', '72', '77'])).
% 1.07/1.29  thf('79', plain,
% 1.07/1.29      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B)
% 1.07/1.29        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29            = (k2_funct_1 @ sk_C)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['66', '78'])).
% 1.07/1.29  thf('80', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('82', plain,
% 1.07/1.29      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.07/1.29        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29            = (k2_funct_1 @ sk_C)))),
% 1.07/1.29      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.07/1.29  thf('83', plain,
% 1.07/1.29      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29         = (k2_funct_1 @ sk_C))),
% 1.07/1.29      inference('simplify', [status(thm)], ['82'])).
% 1.07/1.29  thf('84', plain,
% 1.07/1.29      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.29        (k1_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['65', '83'])).
% 1.07/1.29  thf('85', plain,
% 1.07/1.29      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 1.07/1.29         (k1_relat_1 @ sk_C))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['0', '84'])).
% 1.07/1.29  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('88', plain,
% 1.07/1.29      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.07/1.29        (k1_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.07/1.29  thf(d1_funct_2, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.29       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.29           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.07/1.29             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.07/1.29         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.29           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.07/1.29             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.07/1.29  thf(zf_stmt_1, axiom,
% 1.07/1.29    (![C:$i,B:$i,A:$i]:
% 1.07/1.29     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.07/1.29       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.07/1.29  thf('89', plain,
% 1.07/1.29      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.07/1.29         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 1.07/1.29          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 1.07/1.29          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.07/1.29  thf('90', plain,
% 1.07/1.29      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29           (k2_relat_1 @ sk_C))
% 1.07/1.29        | ((k2_relat_1 @ sk_C)
% 1.07/1.29            = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29               (k2_funct_1 @ sk_C))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['88', '89'])).
% 1.07/1.29  thf('91', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('92', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['5', '53'])).
% 1.07/1.29  thf('93', plain,
% 1.07/1.29      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.29         ((m1_subset_1 @ (k2_tops_2 @ X34 @ X35 @ X36) @ 
% 1.07/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.07/1.29          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.07/1.29          | ~ (v1_funct_2 @ X36 @ X34 @ X35)
% 1.07/1.29          | ~ (v1_funct_1 @ X36))),
% 1.07/1.29      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.07/1.29  thf('94', plain,
% 1.07/1.29      ((~ (v1_funct_1 @ sk_C)
% 1.07/1.29        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.29        | (m1_subset_1 @ 
% 1.07/1.29           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.07/1.29           (k1_zfmisc_1 @ 
% 1.07/1.29            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['92', '93'])).
% 1.07/1.29  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('96', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['62', '63'])).
% 1.07/1.29  thf('97', plain,
% 1.07/1.29      ((m1_subset_1 @ 
% 1.07/1.29        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['94', '95', '96'])).
% 1.07/1.29  thf('98', plain,
% 1.07/1.29      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29         = (k2_funct_1 @ sk_C))),
% 1.07/1.29      inference('simplify', [status(thm)], ['82'])).
% 1.07/1.29  thf('99', plain,
% 1.07/1.29      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['97', '98'])).
% 1.07/1.29  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.07/1.29  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.07/1.29  thf(zf_stmt_4, axiom,
% 1.07/1.29    (![B:$i,A:$i]:
% 1.07/1.29     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.29       ( zip_tseitin_0 @ B @ A ) ))).
% 1.07/1.29  thf(zf_stmt_5, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.29       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.07/1.29         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.29           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.07/1.29             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.07/1.29  thf('100', plain,
% 1.07/1.29      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.07/1.29         (~ (zip_tseitin_0 @ X24 @ X25)
% 1.07/1.29          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 1.07/1.29          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.07/1.29  thf('101', plain,
% 1.07/1.29      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29         (u1_struct_0 @ sk_B))
% 1.07/1.29        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['99', '100'])).
% 1.07/1.29  thf('102', plain,
% 1.07/1.29      (![X19 : $i, X20 : $i]:
% 1.07/1.29         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.07/1.29  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.07/1.29  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.29  thf('104', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.07/1.29      inference('sup+', [status(thm)], ['102', '103'])).
% 1.07/1.29  thf('105', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('106', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['11', '16'])).
% 1.07/1.29  thf(cc3_relset_1, axiom,
% 1.07/1.29    (![A:$i,B:$i]:
% 1.07/1.29     ( ( v1_xboole_0 @ A ) =>
% 1.07/1.29       ( ![C:$i]:
% 1.07/1.29         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.29           ( v1_xboole_0 @ C ) ) ) ))).
% 1.07/1.29  thf('107', plain,
% 1.07/1.29      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.07/1.29         (~ (v1_xboole_0 @ X10)
% 1.07/1.29          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 1.07/1.29          | (v1_xboole_0 @ X11))),
% 1.07/1.29      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.07/1.29  thf('108', plain,
% 1.07/1.29      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['106', '107'])).
% 1.07/1.29  thf(fc11_relat_1, axiom,
% 1.07/1.29    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 1.07/1.29  thf('109', plain,
% 1.07/1.29      (![X2 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X2)) | ~ (v1_xboole_0 @ X2))),
% 1.07/1.29      inference('cnf', [status(esa)], [fc11_relat_1])).
% 1.07/1.29  thf('110', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('clc', [status(thm)], ['36', '37'])).
% 1.07/1.29  thf('111', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.07/1.29      inference('sup-', [status(thm)], ['109', '110'])).
% 1.07/1.29  thf('112', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.07/1.29      inference('clc', [status(thm)], ['108', '111'])).
% 1.07/1.29  thf('113', plain,
% 1.07/1.29      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.07/1.29      inference('sup-', [status(thm)], ['105', '112'])).
% 1.07/1.29  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('115', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['113', '114'])).
% 1.07/1.29  thf('116', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ X0)),
% 1.07/1.29      inference('sup-', [status(thm)], ['104', '115'])).
% 1.07/1.29  thf('117', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('118', plain, (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)),
% 1.07/1.29      inference('demod', [status(thm)], ['116', '117'])).
% 1.07/1.29  thf('119', plain,
% 1.07/1.29      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29        (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['101', '118'])).
% 1.07/1.29  thf('120', plain,
% 1.07/1.29      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29         (k2_struct_0 @ sk_B))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['91', '119'])).
% 1.07/1.29  thf('121', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('122', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('123', plain,
% 1.07/1.29      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29        (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.07/1.29  thf('124', plain,
% 1.07/1.29      (((k2_relat_1 @ sk_C)
% 1.07/1.29         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29            (k2_funct_1 @ sk_C)))),
% 1.07/1.29      inference('demod', [status(thm)], ['90', '123'])).
% 1.07/1.29  thf('125', plain,
% 1.07/1.29      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['97', '98'])).
% 1.07/1.29  thf('126', plain,
% 1.07/1.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.07/1.29         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.07/1.29          | (v1_partfun1 @ X16 @ X17)
% 1.07/1.29          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 1.07/1.29          | ~ (v1_funct_1 @ X16)
% 1.07/1.29          | (v1_xboole_0 @ X18))),
% 1.07/1.29      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.07/1.29  thf('127', plain,
% 1.07/1.29      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.07/1.29        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.07/1.29        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.29             (k1_relat_1 @ sk_C))
% 1.07/1.29        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['125', '126'])).
% 1.07/1.29  thf('128', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('129', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['5', '53'])).
% 1.07/1.29  thf('130', plain,
% 1.07/1.29      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.29         ((v1_funct_1 @ (k2_tops_2 @ X34 @ X35 @ X36))
% 1.07/1.29          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.07/1.29          | ~ (v1_funct_2 @ X36 @ X34 @ X35)
% 1.07/1.29          | ~ (v1_funct_1 @ X36))),
% 1.07/1.29      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.07/1.29  thf('131', plain,
% 1.07/1.29      ((~ (v1_funct_1 @ sk_C)
% 1.07/1.29        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.29        | (v1_funct_1 @ 
% 1.07/1.29           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['129', '130'])).
% 1.07/1.29  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('133', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['62', '63'])).
% 1.07/1.29  thf('134', plain,
% 1.07/1.29      ((v1_funct_1 @ 
% 1.07/1.29        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['131', '132', '133'])).
% 1.07/1.29  thf('135', plain,
% 1.07/1.29      (((v1_funct_1 @ 
% 1.07/1.29         (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['128', '134'])).
% 1.07/1.29  thf('136', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('137', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('138', plain,
% 1.07/1.29      ((v1_funct_1 @ 
% 1.07/1.29        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['135', '136', '137'])).
% 1.07/1.29  thf('139', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('140', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['3', '4'])).
% 1.07/1.29  thf('141', plain,
% 1.07/1.29      (((m1_subset_1 @ sk_C @ 
% 1.07/1.29         (k1_zfmisc_1 @ 
% 1.07/1.29          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['139', '140'])).
% 1.07/1.29  thf('142', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('143', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['141', '142'])).
% 1.07/1.29  thf('144', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('145', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['143', '144'])).
% 1.07/1.29  thf('146', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('147', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['145', '146'])).
% 1.07/1.29  thf('148', plain,
% 1.07/1.29      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.07/1.29         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 1.07/1.29          | ~ (v2_funct_1 @ X33)
% 1.07/1.29          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 1.07/1.29          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.07/1.29          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 1.07/1.29          | ~ (v1_funct_1 @ X33))),
% 1.07/1.29      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.07/1.29  thf('149', plain,
% 1.07/1.29      ((~ (v1_funct_1 @ sk_C)
% 1.07/1.29        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.07/1.29        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.29            = (k2_funct_1 @ sk_C))
% 1.07/1.29        | ~ (v2_funct_1 @ sk_C)
% 1.07/1.29        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.29            != (k2_relat_1 @ sk_C)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['147', '148'])).
% 1.07/1.29  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('151', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('152', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['60', '61'])).
% 1.07/1.29  thf('153', plain,
% 1.07/1.29      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['151', '152'])).
% 1.07/1.29  thf('154', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('155', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['153', '154'])).
% 1.07/1.29  thf('156', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('157', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['155', '156'])).
% 1.07/1.29  thf('158', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('159', plain,
% 1.07/1.29      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['157', '158'])).
% 1.07/1.29  thf('160', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('161', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('162', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('163', plain,
% 1.07/1.29      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29         = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('164', plain,
% 1.07/1.29      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29          = (k2_struct_0 @ sk_B))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_A))),
% 1.07/1.29      inference('sup+', [status(thm)], ['162', '163'])).
% 1.07/1.29  thf('165', plain, ((l1_struct_0 @ sk_A)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('166', plain,
% 1.07/1.29      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29         = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['164', '165'])).
% 1.07/1.29  thf('167', plain,
% 1.07/1.29      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29          = (k2_struct_0 @ sk_B))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['161', '166'])).
% 1.07/1.29  thf('168', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('169', plain,
% 1.07/1.29      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.07/1.29         = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['167', '168'])).
% 1.07/1.29  thf('170', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('171', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('172', plain,
% 1.07/1.29      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.29         = (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['169', '170', '171'])).
% 1.07/1.29  thf('173', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('174', plain,
% 1.07/1.29      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.29         = (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['172', '173'])).
% 1.07/1.29  thf('175', plain,
% 1.07/1.29      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.29          = (k2_funct_1 @ sk_C))
% 1.07/1.29        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.07/1.29      inference('demod', [status(thm)], ['149', '150', '159', '160', '174'])).
% 1.07/1.29  thf('176', plain,
% 1.07/1.29      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.29         = (k2_funct_1 @ sk_C))),
% 1.07/1.29      inference('simplify', [status(thm)], ['175'])).
% 1.07/1.29  thf('177', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['138', '176'])).
% 1.07/1.29  thf('178', plain,
% 1.07/1.29      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.07/1.29        (k1_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['65', '83'])).
% 1.07/1.29  thf('179', plain,
% 1.07/1.29      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.07/1.29        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.07/1.29      inference('demod', [status(thm)], ['127', '177', '178'])).
% 1.07/1.29  thf('180', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['113', '114'])).
% 1.07/1.29  thf('181', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('182', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['180', '181'])).
% 1.07/1.29  thf('183', plain,
% 1.07/1.29      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('clc', [status(thm)], ['179', '182'])).
% 1.07/1.29  thf('184', plain,
% 1.07/1.29      (![X27 : $i, X28 : $i]:
% 1.07/1.29         (~ (v1_partfun1 @ X28 @ X27)
% 1.07/1.29          | ((k1_relat_1 @ X28) = (X27))
% 1.07/1.29          | ~ (v4_relat_1 @ X28 @ X27)
% 1.07/1.29          | ~ (v1_relat_1 @ X28))),
% 1.07/1.29      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.07/1.29  thf('185', plain,
% 1.07/1.29      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.07/1.29        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.07/1.29        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['183', '184'])).
% 1.07/1.29  thf('186', plain,
% 1.07/1.29      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['97', '98'])).
% 1.07/1.29  thf('187', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i]:
% 1.07/1.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.29          | (v1_relat_1 @ X0)
% 1.07/1.29          | ~ (v1_relat_1 @ X1))),
% 1.07/1.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.29  thf('188', plain,
% 1.07/1.29      ((~ (v1_relat_1 @ 
% 1.07/1.29           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))
% 1.07/1.29        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['186', '187'])).
% 1.07/1.29  thf('189', plain,
% 1.07/1.29      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.07/1.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.29  thf('190', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['188', '189'])).
% 1.07/1.29  thf('191', plain,
% 1.07/1.29      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['97', '98'])).
% 1.07/1.29  thf('192', plain,
% 1.07/1.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.07/1.29         ((v4_relat_1 @ X7 @ X8)
% 1.07/1.29          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.07/1.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.29  thf('193', plain,
% 1.07/1.29      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup-', [status(thm)], ['191', '192'])).
% 1.07/1.29  thf(t55_funct_1, axiom,
% 1.07/1.29    (![A:$i]:
% 1.07/1.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.29       ( ( v2_funct_1 @ A ) =>
% 1.07/1.29         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.07/1.29           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.07/1.29  thf('194', plain,
% 1.07/1.29      (![X6 : $i]:
% 1.07/1.29         (~ (v2_funct_1 @ X6)
% 1.07/1.29          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 1.07/1.29          | ~ (v1_funct_1 @ X6)
% 1.07/1.29          | ~ (v1_relat_1 @ X6))),
% 1.07/1.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.07/1.29  thf('195', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('196', plain,
% 1.07/1.29      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup-', [status(thm)], ['191', '192'])).
% 1.07/1.29  thf('197', plain,
% 1.07/1.29      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['195', '196'])).
% 1.07/1.29  thf('198', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('199', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('200', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['197', '198', '199'])).
% 1.07/1.29  thf('201', plain,
% 1.07/1.29      (![X6 : $i]:
% 1.07/1.29         (~ (v2_funct_1 @ X6)
% 1.07/1.29          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 1.07/1.29          | ~ (v1_funct_1 @ X6)
% 1.07/1.29          | ~ (v1_relat_1 @ X6))),
% 1.07/1.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.07/1.29  thf('202', plain,
% 1.07/1.29      (![X27 : $i, X28 : $i]:
% 1.07/1.29         (((k1_relat_1 @ X28) != (X27))
% 1.07/1.29          | (v1_partfun1 @ X28 @ X27)
% 1.07/1.29          | ~ (v4_relat_1 @ X28 @ X27)
% 1.07/1.29          | ~ (v1_relat_1 @ X28))),
% 1.07/1.29      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.07/1.29  thf('203', plain,
% 1.07/1.29      (![X28 : $i]:
% 1.07/1.29         (~ (v1_relat_1 @ X28)
% 1.07/1.29          | ~ (v4_relat_1 @ X28 @ (k1_relat_1 @ X28))
% 1.07/1.29          | (v1_partfun1 @ X28 @ (k1_relat_1 @ X28)))),
% 1.07/1.29      inference('simplify', [status(thm)], ['202'])).
% 1.07/1.29  thf('204', plain,
% 1.07/1.29      (![X0 : $i]:
% 1.07/1.29         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.07/1.29          | ~ (v1_relat_1 @ X0)
% 1.07/1.29          | ~ (v1_funct_1 @ X0)
% 1.07/1.29          | ~ (v2_funct_1 @ X0)
% 1.07/1.29          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['201', '203'])).
% 1.07/1.29  thf('205', plain,
% 1.07/1.29      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.07/1.29        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.29           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.07/1.29        | ~ (v2_funct_1 @ sk_C)
% 1.07/1.29        | ~ (v1_funct_1 @ sk_C)
% 1.07/1.29        | ~ (v1_relat_1 @ sk_C))),
% 1.07/1.29      inference('sup-', [status(thm)], ['200', '204'])).
% 1.07/1.29  thf('206', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['188', '189'])).
% 1.07/1.29  thf('207', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('208', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.29      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.29  thf('210', plain,
% 1.07/1.29      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.07/1.29      inference('demod', [status(thm)], ['205', '206', '207', '208', '209'])).
% 1.07/1.29  thf('211', plain,
% 1.07/1.29      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.07/1.29        | ~ (v1_relat_1 @ sk_C)
% 1.07/1.29        | ~ (v1_funct_1 @ sk_C)
% 1.07/1.29        | ~ (v2_funct_1 @ sk_C))),
% 1.07/1.29      inference('sup+', [status(thm)], ['194', '210'])).
% 1.07/1.29  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.29      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.29  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('215', plain,
% 1.07/1.29      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['211', '212', '213', '214'])).
% 1.07/1.29  thf('216', plain,
% 1.07/1.29      (![X27 : $i, X28 : $i]:
% 1.07/1.29         (~ (v1_partfun1 @ X28 @ X27)
% 1.07/1.29          | ((k1_relat_1 @ X28) = (X27))
% 1.07/1.29          | ~ (v4_relat_1 @ X28 @ X27)
% 1.07/1.29          | ~ (v1_relat_1 @ X28))),
% 1.07/1.29      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.07/1.29  thf('217', plain,
% 1.07/1.29      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.07/1.29        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.07/1.29        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['215', '216'])).
% 1.07/1.29  thf('218', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['188', '189'])).
% 1.07/1.29  thf('219', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['197', '198', '199'])).
% 1.07/1.29  thf('220', plain,
% 1.07/1.29      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('demod', [status(thm)], ['217', '218', '219'])).
% 1.07/1.29  thf('221', plain, (((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B))),
% 1.07/1.29      inference('demod', [status(thm)], ['185', '190', '193', '220'])).
% 1.07/1.29  thf('222', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('223', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('224', plain,
% 1.07/1.29      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          != (k2_struct_0 @ sk_B))
% 1.07/1.29        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29            != (k2_struct_0 @ sk_A)))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('225', plain,
% 1.07/1.29      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          != (k2_struct_0 @ sk_B)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('split', [status(esa)], ['224'])).
% 1.07/1.29  thf('226', plain,
% 1.07/1.29      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.07/1.29           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29           != (k2_struct_0 @ sk_B))
% 1.07/1.29         | ~ (l1_struct_0 @ sk_A)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['223', '225'])).
% 1.07/1.29  thf('227', plain, ((l1_struct_0 @ sk_A)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('228', plain,
% 1.07/1.29      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          != (k2_struct_0 @ sk_B)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['226', '227'])).
% 1.07/1.29  thf('229', plain,
% 1.07/1.29      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.07/1.29           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29           != (k2_struct_0 @ sk_B))
% 1.07/1.29         | ~ (l1_struct_0 @ sk_B)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['222', '228'])).
% 1.07/1.29  thf('230', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('231', plain,
% 1.07/1.29      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          != (k2_struct_0 @ sk_B)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['229', '230'])).
% 1.07/1.29  thf('232', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('233', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('234', plain,
% 1.07/1.29      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          != (k2_relat_1 @ sk_C)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['231', '232', '233'])).
% 1.07/1.29  thf('235', plain,
% 1.07/1.29      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.07/1.29          != (k2_relat_1 @ sk_C)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['221', '234'])).
% 1.07/1.29  thf('236', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('237', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.07/1.29      inference('clc', [status(thm)], ['28', '38'])).
% 1.07/1.29  thf('238', plain,
% 1.07/1.29      (![X27 : $i, X28 : $i]:
% 1.07/1.29         (~ (v1_partfun1 @ X28 @ X27)
% 1.07/1.29          | ((k1_relat_1 @ X28) = (X27))
% 1.07/1.29          | ~ (v4_relat_1 @ X28 @ X27)
% 1.07/1.29          | ~ (v1_relat_1 @ X28))),
% 1.07/1.29      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.07/1.29  thf('239', plain,
% 1.07/1.29      ((~ (v1_relat_1 @ sk_C)
% 1.07/1.29        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.07/1.29        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['237', '238'])).
% 1.07/1.29  thf('240', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.29      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.29  thf('241', plain,
% 1.07/1.29      ((m1_subset_1 @ sk_C @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('242', plain,
% 1.07/1.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.07/1.29         ((v4_relat_1 @ X7 @ X8)
% 1.07/1.29          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.07/1.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.29  thf('243', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.07/1.29      inference('sup-', [status(thm)], ['241', '242'])).
% 1.07/1.29  thf('244', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['239', '240', '243'])).
% 1.07/1.29  thf('245', plain,
% 1.07/1.29      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.29         = (k2_funct_1 @ sk_C))),
% 1.07/1.29      inference('simplify', [status(thm)], ['175'])).
% 1.07/1.29  thf('246', plain,
% 1.07/1.29      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_B))))),
% 1.07/1.29      inference('demod', [status(thm)], ['235', '236', '244', '245'])).
% 1.07/1.29  thf('247', plain,
% 1.07/1.29      (![X6 : $i]:
% 1.07/1.29         (~ (v2_funct_1 @ X6)
% 1.07/1.29          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 1.07/1.29          | ~ (v1_funct_1 @ X6)
% 1.07/1.29          | ~ (v1_relat_1 @ X6))),
% 1.07/1.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.07/1.29  thf('248', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('249', plain,
% 1.07/1.29      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['97', '98'])).
% 1.07/1.29  thf('250', plain,
% 1.07/1.29      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.29         (k1_zfmisc_1 @ 
% 1.07/1.29          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.07/1.29        | ~ (l1_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['248', '249'])).
% 1.07/1.29  thf('251', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('252', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('253', plain,
% 1.07/1.29      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.07/1.29        (k1_zfmisc_1 @ 
% 1.07/1.29         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.07/1.29      inference('demod', [status(thm)], ['250', '251', '252'])).
% 1.07/1.29  thf('254', plain,
% 1.07/1.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.07/1.29         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.07/1.29          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.07/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.29  thf('255', plain,
% 1.07/1.29      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['253', '254'])).
% 1.07/1.29  thf('256', plain,
% 1.07/1.29      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.07/1.29         = (k2_funct_1 @ sk_C))),
% 1.07/1.29      inference('simplify', [status(thm)], ['175'])).
% 1.07/1.29  thf('257', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('258', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('259', plain,
% 1.07/1.29      (![X29 : $i]:
% 1.07/1.29         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.07/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.29  thf('260', plain,
% 1.07/1.29      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          != (k2_struct_0 @ sk_A)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('split', [status(esa)], ['224'])).
% 1.07/1.29  thf('261', plain,
% 1.07/1.29      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29           != (k2_struct_0 @ sk_A))
% 1.07/1.29         | ~ (l1_struct_0 @ sk_B)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['259', '260'])).
% 1.07/1.29  thf('262', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('263', plain,
% 1.07/1.29      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          != (k2_struct_0 @ sk_A)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('demod', [status(thm)], ['261', '262'])).
% 1.07/1.29  thf('264', plain,
% 1.07/1.29      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29           != (k2_struct_0 @ sk_A))
% 1.07/1.29         | ~ (l1_struct_0 @ sk_B)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['258', '263'])).
% 1.07/1.29  thf('265', plain, ((l1_struct_0 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('266', plain,
% 1.07/1.29      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          != (k2_struct_0 @ sk_A)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('demod', [status(thm)], ['264', '265'])).
% 1.07/1.29  thf('267', plain,
% 1.07/1.29      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.07/1.29          != (k2_struct_0 @ sk_A)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['257', '266'])).
% 1.07/1.29  thf('268', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.07/1.29      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.29  thf('269', plain,
% 1.07/1.29      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.07/1.29          != (k2_struct_0 @ sk_A)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('demod', [status(thm)], ['267', '268'])).
% 1.07/1.29  thf('270', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['239', '240', '243'])).
% 1.07/1.29  thf('271', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['239', '240', '243'])).
% 1.07/1.29  thf('272', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.07/1.29      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.07/1.29  thf('273', plain,
% 1.07/1.29      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.07/1.29          != (k1_relat_1 @ sk_C)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('demod', [status(thm)], ['269', '270', '271', '272'])).
% 1.07/1.29  thf('274', plain,
% 1.07/1.29      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['256', '273'])).
% 1.07/1.29  thf('275', plain,
% 1.07/1.29      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['255', '274'])).
% 1.07/1.29  thf('276', plain,
% 1.07/1.29      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.07/1.29         | ~ (v1_relat_1 @ sk_C)
% 1.07/1.29         | ~ (v1_funct_1 @ sk_C)
% 1.07/1.29         | ~ (v2_funct_1 @ sk_C)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('sup-', [status(thm)], ['247', '275'])).
% 1.07/1.29  thf('277', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.29      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.29  thf('278', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('279', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('280', plain,
% 1.07/1.29      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.07/1.29         <= (~
% 1.07/1.29             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29                = (k2_struct_0 @ sk_A))))),
% 1.07/1.29      inference('demod', [status(thm)], ['276', '277', '278', '279'])).
% 1.07/1.29  thf('281', plain,
% 1.07/1.29      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          = (k2_struct_0 @ sk_A)))),
% 1.07/1.29      inference('simplify', [status(thm)], ['280'])).
% 1.07/1.29  thf('282', plain,
% 1.07/1.29      (~
% 1.07/1.29       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          = (k2_struct_0 @ sk_B))) | 
% 1.07/1.29       ~
% 1.07/1.29       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          = (k2_struct_0 @ sk_A)))),
% 1.07/1.29      inference('split', [status(esa)], ['224'])).
% 1.07/1.29  thf('283', plain,
% 1.07/1.29      (~
% 1.07/1.29       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.07/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.07/1.29          = (k2_struct_0 @ sk_B)))),
% 1.07/1.29      inference('sat_resolution*', [status(thm)], ['281', '282'])).
% 1.07/1.29  thf('284', plain,
% 1.07/1.29      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.07/1.29         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.07/1.29      inference('simpl_trail', [status(thm)], ['246', '283'])).
% 1.07/1.29  thf('285', plain, ($false),
% 1.07/1.29      inference('simplify_reflect-', [status(thm)], ['124', '284'])).
% 1.07/1.29  
% 1.07/1.29  % SZS output end Refutation
% 1.07/1.29  
% 1.07/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
