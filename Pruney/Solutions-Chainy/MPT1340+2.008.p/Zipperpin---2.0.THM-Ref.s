%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uIkAI2Q6A6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:06 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  280 (1916 expanded)
%              Number of leaves         :   43 ( 568 expanded)
%              Depth                    :   35
%              Number of atoms          : 2593 (42798 expanded)
%              Number of equality atoms :  128 (1282 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
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

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41','44'])).

thf('46',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('48',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('54',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
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

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','60'])).

thf('62',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','61'])).

thf('63',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','61'])).

thf('64',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','61'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('66',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','62','63','64','65'])).

thf('67',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

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

thf('74',plain,(
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

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('100',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','87','88','100'])).

thf('102',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['66','102'])).

thf('104',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','103'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('108',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

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

thf('110',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('114',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
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

thf('119',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('121',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('130',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X26 ) @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('131',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('134',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('141',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('144',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('145',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('147',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['127'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('158',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('162',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('163',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['160','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['159','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['158','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['157','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['156','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['174','175','176','177'])).

thf('179',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['155','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['140','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('190',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','60'])).

thf('195',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['127'])).

thf('196',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['190','191','192','193','194','195'])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','200'])).

thf('202',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','60'])).

thf('203',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202','203','204','205'])).

thf('207',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('209',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('210',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','128','137','207','210'])).

thf('212',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['108','211'])).

thf('213',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','60'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['212','213','214','215','216'])).

thf('218',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['107','218'])).

thf('220',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','219'])).

thf('221',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('222',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('223',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_funct_2 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['221','227'])).

thf('229',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('231',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('233',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    $false ),
    inference(demod,[status(thm)],['220','231','232','233','234'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uIkAI2Q6A6
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.62  % Solved by: fo/fo7.sh
% 0.34/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.62  % done 297 iterations in 0.152s
% 0.34/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.62  % SZS output start Refutation
% 0.34/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.34/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.34/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.34/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.34/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.34/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.34/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.34/0.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.34/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.62  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.34/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.62  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.34/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.34/0.62  thf(t65_funct_1, axiom,
% 0.34/0.62    (![A:$i]:
% 0.34/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.34/0.62  thf('0', plain,
% 0.34/0.62      (![X7 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X7)
% 0.34/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.34/0.62          | ~ (v1_funct_1 @ X7)
% 0.34/0.62          | ~ (v1_relat_1 @ X7))),
% 0.34/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.34/0.62  thf(d3_struct_0, axiom,
% 0.34/0.62    (![A:$i]:
% 0.34/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.34/0.62  thf('1', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('2', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf(t64_tops_2, conjecture,
% 0.34/0.62    (![A:$i]:
% 0.34/0.62     ( ( l1_struct_0 @ A ) =>
% 0.34/0.62       ( ![B:$i]:
% 0.34/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.34/0.62           ( ![C:$i]:
% 0.34/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.34/0.62                 ( m1_subset_1 @
% 0.34/0.62                   C @ 
% 0.34/0.62                   ( k1_zfmisc_1 @
% 0.34/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.34/0.62               ( ( ( ( k2_relset_1 @
% 0.34/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.34/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.34/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.34/0.62                 ( r2_funct_2 @
% 0.34/0.62                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.34/0.62                   ( k2_tops_2 @
% 0.34/0.62                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.34/0.62                     ( k2_tops_2 @
% 0.34/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.34/0.62                   C ) ) ) ) ) ) ))).
% 0.34/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.62    (~( ![A:$i]:
% 0.34/0.62        ( ( l1_struct_0 @ A ) =>
% 0.34/0.62          ( ![B:$i]:
% 0.34/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.34/0.62              ( ![C:$i]:
% 0.34/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.34/0.62                    ( v1_funct_2 @
% 0.34/0.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.34/0.62                    ( m1_subset_1 @
% 0.34/0.62                      C @ 
% 0.34/0.62                      ( k1_zfmisc_1 @
% 0.34/0.62                        ( k2_zfmisc_1 @
% 0.34/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.34/0.62                  ( ( ( ( k2_relset_1 @
% 0.34/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.34/0.62                        ( k2_struct_0 @ B ) ) & 
% 0.34/0.62                      ( v2_funct_1 @ C ) ) =>
% 0.34/0.62                    ( r2_funct_2 @
% 0.34/0.62                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.34/0.62                      ( k2_tops_2 @
% 0.34/0.62                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.34/0.62                        ( k2_tops_2 @
% 0.34/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.34/0.62                      C ) ) ) ) ) ) ) )),
% 0.34/0.62    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.34/0.62  thf('3', plain,
% 0.34/0.62      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.34/0.62          sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('4', plain,
% 0.34/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.34/0.62           sk_C)
% 0.34/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.62  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('6', plain,
% 0.34/0.62      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.34/0.62          sk_C)),
% 0.34/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.34/0.62  thf('7', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('8', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('9', plain,
% 0.34/0.62      (((m1_subset_1 @ sk_C @ 
% 0.34/0.62         (k1_zfmisc_1 @ 
% 0.34/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.34/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.34/0.62  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('11', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.34/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.34/0.62  thf('12', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.34/0.62    (![A:$i,B:$i,C:$i]:
% 0.34/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.34/0.62  thf('13', plain,
% 0.34/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.34/0.62         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.34/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.34/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.34/0.62  thf('14', plain,
% 0.34/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.34/0.62         = (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.62  thf('15', plain,
% 0.34/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.34/0.62         = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.34/0.62  thf('17', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.34/0.62      inference('demod', [status(thm)], ['11', '16'])).
% 0.34/0.62  thf(cc5_funct_2, axiom,
% 0.34/0.62    (![A:$i,B:$i]:
% 0.34/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.34/0.62       ( ![C:$i]:
% 0.34/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.62           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.34/0.62             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.34/0.62  thf('18', plain,
% 0.34/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.34/0.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.34/0.62          | (v1_partfun1 @ X17 @ X18)
% 0.34/0.62          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.34/0.62          | ~ (v1_funct_1 @ X17)
% 0.34/0.62          | (v1_xboole_0 @ X19))),
% 0.34/0.62      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.34/0.62  thf('19', plain,
% 0.34/0.62      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.34/0.62        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.34/0.62  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('21', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('22', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('23', plain,
% 0.34/0.62      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.34/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.34/0.62  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('25', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.34/0.62  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.34/0.62  thf('27', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.34/0.62  thf('28', plain,
% 0.34/0.62      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.34/0.62        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.34/0.62      inference('demod', [status(thm)], ['19', '20', '27'])).
% 0.34/0.62  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.34/0.62  thf(fc5_struct_0, axiom,
% 0.34/0.62    (![A:$i]:
% 0.34/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.34/0.62       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.34/0.62  thf('30', plain,
% 0.34/0.62      (![X30 : $i]:
% 0.34/0.62         (~ (v1_xboole_0 @ (k2_struct_0 @ X30))
% 0.34/0.62          | ~ (l1_struct_0 @ X30)
% 0.34/0.62          | (v2_struct_0 @ X30))),
% 0.34/0.62      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.34/0.62  thf('31', plain,
% 0.34/0.62      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.34/0.62        | (v2_struct_0 @ sk_B)
% 0.34/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.34/0.62  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('33', plain,
% 0.34/0.62      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.34/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.34/0.62  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('35', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('clc', [status(thm)], ['33', '34'])).
% 0.34/0.62  thf('36', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.34/0.62      inference('clc', [status(thm)], ['28', '35'])).
% 0.34/0.62  thf(d4_partfun1, axiom,
% 0.34/0.62    (![A:$i,B:$i]:
% 0.34/0.62     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.34/0.62       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.34/0.62  thf('37', plain,
% 0.34/0.62      (![X20 : $i, X21 : $i]:
% 0.34/0.62         (~ (v1_partfun1 @ X21 @ X20)
% 0.34/0.62          | ((k1_relat_1 @ X21) = (X20))
% 0.34/0.62          | ~ (v4_relat_1 @ X21 @ X20)
% 0.34/0.62          | ~ (v1_relat_1 @ X21))),
% 0.34/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.34/0.62  thf('38', plain,
% 0.34/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.34/0.62        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.34/0.62  thf('39', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf(cc1_relset_1, axiom,
% 0.34/0.62    (![A:$i,B:$i,C:$i]:
% 0.34/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.62       ( v1_relat_1 @ C ) ))).
% 0.34/0.62  thf('40', plain,
% 0.34/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.34/0.62         ((v1_relat_1 @ X8)
% 0.34/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.34/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.34/0.62  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('42', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf(cc2_relset_1, axiom,
% 0.34/0.62    (![A:$i,B:$i,C:$i]:
% 0.34/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.62  thf('43', plain,
% 0.34/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.34/0.62         ((v4_relat_1 @ X11 @ X12)
% 0.34/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.34/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.62  thf('44', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.34/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.34/0.62  thf('45', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.34/0.62      inference('demod', [status(thm)], ['38', '41', '44'])).
% 0.34/0.62  thf('46', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('47', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.34/0.62      inference('clc', [status(thm)], ['28', '35'])).
% 0.34/0.62  thf('48', plain,
% 0.34/0.62      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.34/0.62      inference('sup+', [status(thm)], ['46', '47'])).
% 0.34/0.62  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('50', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.34/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.34/0.62  thf('51', plain,
% 0.34/0.62      (![X20 : $i, X21 : $i]:
% 0.34/0.62         (~ (v1_partfun1 @ X21 @ X20)
% 0.34/0.62          | ((k1_relat_1 @ X21) = (X20))
% 0.34/0.62          | ~ (v4_relat_1 @ X21 @ X20)
% 0.34/0.62          | ~ (v1_relat_1 @ X21))),
% 0.34/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.34/0.62  thf('52', plain,
% 0.34/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.34/0.62        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.34/0.62  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('54', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('55', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('56', plain,
% 0.34/0.62      (((m1_subset_1 @ sk_C @ 
% 0.34/0.62         (k1_zfmisc_1 @ 
% 0.34/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.34/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.34/0.62      inference('sup+', [status(thm)], ['54', '55'])).
% 0.34/0.62  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('58', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.34/0.62  thf('59', plain,
% 0.34/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.34/0.62         ((v4_relat_1 @ X11 @ X12)
% 0.34/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.34/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.62  thf('60', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.34/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.34/0.62  thf('61', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.34/0.62      inference('demod', [status(thm)], ['52', '53', '60'])).
% 0.34/0.62  thf('62', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.34/0.62      inference('demod', [status(thm)], ['45', '61'])).
% 0.34/0.62  thf('63', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.34/0.62      inference('demod', [status(thm)], ['45', '61'])).
% 0.34/0.62  thf('64', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.34/0.62      inference('demod', [status(thm)], ['45', '61'])).
% 0.34/0.62  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.34/0.62  thf('66', plain,
% 0.34/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.34/0.62          sk_C)),
% 0.34/0.62      inference('demod', [status(thm)], ['6', '62', '63', '64', '65'])).
% 0.34/0.62  thf('67', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('68', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.34/0.62  thf('69', plain,
% 0.34/0.62      (((m1_subset_1 @ sk_C @ 
% 0.34/0.62         (k1_zfmisc_1 @ 
% 0.34/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.34/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['67', '68'])).
% 0.34/0.62  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('71', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.34/0.62      inference('demod', [status(thm)], ['69', '70'])).
% 0.34/0.62  thf('72', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.34/0.62  thf('73', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.34/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.34/0.62  thf(d4_tops_2, axiom,
% 0.34/0.62    (![A:$i,B:$i,C:$i]:
% 0.34/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.34/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.34/0.62         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.34/0.62  thf('74', plain,
% 0.34/0.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.34/0.62         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.34/0.62          | ~ (v2_funct_1 @ X33)
% 0.34/0.62          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.34/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.34/0.62          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.34/0.62          | ~ (v1_funct_1 @ X33))),
% 0.34/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.34/0.62  thf('75', plain,
% 0.34/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.34/0.62        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62            = (k2_funct_1 @ sk_C))
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.34/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62            != (k2_relat_1 @ sk_C)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.34/0.62  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('77', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('78', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('79', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('80', plain,
% 0.34/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.34/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.34/0.62      inference('sup+', [status(thm)], ['78', '79'])).
% 0.34/0.62  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('82', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.34/0.62      inference('demod', [status(thm)], ['80', '81'])).
% 0.34/0.62  thf('83', plain,
% 0.34/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.34/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['77', '82'])).
% 0.34/0.62  thf('84', plain, ((l1_struct_0 @ sk_B)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('85', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('demod', [status(thm)], ['83', '84'])).
% 0.34/0.62  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.34/0.62  thf('87', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.34/0.62  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('89', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('90', plain,
% 0.34/0.62      (![X29 : $i]:
% 0.34/0.62         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.34/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.34/0.62  thf('91', plain,
% 0.34/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.34/0.62         = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('92', plain,
% 0.34/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.34/0.62          = (k2_struct_0 @ sk_B))
% 0.34/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.34/0.62      inference('sup+', [status(thm)], ['90', '91'])).
% 0.34/0.62  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('94', plain,
% 0.34/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.34/0.62         = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('demod', [status(thm)], ['92', '93'])).
% 0.34/0.62  thf('95', plain,
% 0.34/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.34/0.62          = (k2_struct_0 @ sk_B))
% 0.34/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['89', '94'])).
% 0.34/0.62  thf('96', plain, ((l1_struct_0 @ sk_B)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('97', plain,
% 0.34/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.34/0.62         = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('demod', [status(thm)], ['95', '96'])).
% 0.34/0.62  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.34/0.62  thf('99', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.34/0.62  thf('100', plain,
% 0.34/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62         = (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.34/0.62  thf('101', plain,
% 0.34/0.62      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62          = (k2_funct_1 @ sk_C))
% 0.34/0.62        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.34/0.62      inference('demod', [status(thm)], ['75', '76', '87', '88', '100'])).
% 0.34/0.62  thf('102', plain,
% 0.34/0.62      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62         = (k2_funct_1 @ sk_C))),
% 0.34/0.62      inference('simplify', [status(thm)], ['101'])).
% 0.34/0.62  thf('103', plain,
% 0.34/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62           (k2_funct_1 @ sk_C)) @ 
% 0.34/0.62          sk_C)),
% 0.34/0.62      inference('demod', [status(thm)], ['66', '102'])).
% 0.34/0.62  thf('104', plain,
% 0.34/0.62      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.62           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62            (k2_funct_1 @ sk_C)) @ 
% 0.34/0.62           sk_C)
% 0.34/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup-', [status(thm)], ['1', '103'])).
% 0.34/0.62  thf('105', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.34/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.34/0.62  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('107', plain,
% 0.34/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.62          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62           (k2_funct_1 @ sk_C)) @ 
% 0.34/0.62          sk_C)),
% 0.34/0.62      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.34/0.62  thf(t55_funct_1, axiom,
% 0.34/0.62    (![A:$i]:
% 0.34/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.62       ( ( v2_funct_1 @ A ) =>
% 0.34/0.62         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.34/0.62           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.34/0.62  thf('108', plain,
% 0.34/0.62      (![X5 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X5)
% 0.34/0.62          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.34/0.62          | ~ (v1_funct_1 @ X5)
% 0.34/0.62          | ~ (v1_relat_1 @ X5))),
% 0.34/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.34/0.62  thf('109', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.34/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.34/0.62  thf(t31_funct_2, axiom,
% 0.34/0.62    (![A:$i,B:$i,C:$i]:
% 0.34/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.34/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.34/0.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.34/0.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.34/0.62           ( m1_subset_1 @
% 0.34/0.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.34/0.62  thf('110', plain,
% 0.34/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X26)
% 0.34/0.62          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.34/0.62          | (m1_subset_1 @ (k2_funct_1 @ X26) @ 
% 0.34/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.34/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.34/0.62          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.34/0.62          | ~ (v1_funct_1 @ X26))),
% 0.34/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.34/0.62  thf('111', plain,
% 0.34/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.34/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.34/0.62           (k1_zfmisc_1 @ 
% 0.34/0.62            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.34/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62            != (k2_relat_1 @ sk_C))
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.34/0.62      inference('sup-', [status(thm)], ['109', '110'])).
% 0.34/0.62  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('113', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.34/0.62  thf('114', plain,
% 0.34/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62         = (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.34/0.62  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('116', plain,
% 0.34/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.34/0.62         (k1_zfmisc_1 @ 
% 0.34/0.62          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.34/0.62        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.34/0.62      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 0.34/0.62  thf('117', plain,
% 0.34/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.34/0.62      inference('simplify', [status(thm)], ['116'])).
% 0.34/0.62  thf('118', plain,
% 0.34/0.62      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.34/0.62         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.34/0.62          | ~ (v2_funct_1 @ X33)
% 0.34/0.62          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.34/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.34/0.62          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.34/0.62          | ~ (v1_funct_1 @ X33))),
% 0.34/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.34/0.62  thf('119', plain,
% 0.34/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.34/0.62             (k2_struct_0 @ sk_A))
% 0.34/0.62        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.34/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['117', '118'])).
% 0.34/0.62  thf('120', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.34/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.34/0.62  thf('121', plain,
% 0.34/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X26)
% 0.34/0.62          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.34/0.62          | (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.34/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.34/0.62          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.34/0.62          | ~ (v1_funct_1 @ X26))),
% 0.34/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.34/0.62  thf('122', plain,
% 0.34/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.34/0.62        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62            != (k2_relat_1 @ sk_C))
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.34/0.62      inference('sup-', [status(thm)], ['120', '121'])).
% 0.34/0.62  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('124', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.34/0.62  thf('125', plain,
% 0.34/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62         = (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.34/0.62  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('127', plain,
% 0.34/0.62      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.34/0.62      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.34/0.62  thf('128', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.34/0.62      inference('simplify', [status(thm)], ['127'])).
% 0.34/0.62  thf('129', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.34/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.34/0.62  thf('130', plain,
% 0.34/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X26)
% 0.34/0.62          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.34/0.62          | (v1_funct_2 @ (k2_funct_1 @ X26) @ X27 @ X28)
% 0.34/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.34/0.62          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.34/0.62          | ~ (v1_funct_1 @ X26))),
% 0.34/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.34/0.62  thf('131', plain,
% 0.34/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.34/0.62        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.34/0.62           (k2_struct_0 @ sk_A))
% 0.34/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62            != (k2_relat_1 @ sk_C))
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.34/0.62      inference('sup-', [status(thm)], ['129', '130'])).
% 0.34/0.62  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('133', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.34/0.62  thf('134', plain,
% 0.34/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.34/0.62         = (k2_relat_1 @ sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.34/0.62  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('136', plain,
% 0.34/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.34/0.62         (k2_struct_0 @ sk_A))
% 0.34/0.62        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.34/0.62      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 0.34/0.62  thf('137', plain,
% 0.34/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.34/0.62        (k2_struct_0 @ sk_A))),
% 0.34/0.62      inference('simplify', [status(thm)], ['136'])).
% 0.34/0.62  thf('138', plain,
% 0.34/0.62      (![X5 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X5)
% 0.34/0.62          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.34/0.62          | ~ (v1_funct_1 @ X5)
% 0.34/0.62          | ~ (v1_relat_1 @ X5))),
% 0.34/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.34/0.62  thf(dt_k2_funct_1, axiom,
% 0.34/0.62    (![A:$i]:
% 0.34/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.34/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.34/0.62  thf('139', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.34/0.62  thf('140', plain,
% 0.34/0.62      (![X7 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X7)
% 0.34/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.34/0.62          | ~ (v1_funct_1 @ X7)
% 0.34/0.62          | ~ (v1_relat_1 @ X7))),
% 0.34/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.34/0.62  thf('141', plain,
% 0.34/0.62      (![X5 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X5)
% 0.34/0.62          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.34/0.62          | ~ (v1_funct_1 @ X5)
% 0.34/0.62          | ~ (v1_relat_1 @ X5))),
% 0.34/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.34/0.62  thf('142', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.34/0.62  thf('143', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.34/0.62  thf(t61_funct_1, axiom,
% 0.34/0.62    (![A:$i]:
% 0.34/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.62       ( ( v2_funct_1 @ A ) =>
% 0.34/0.62         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.34/0.62             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.34/0.62           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.34/0.62             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.34/0.62  thf('144', plain,
% 0.34/0.62      (![X6 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X6)
% 0.34/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.34/0.62              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.34/0.62          | ~ (v1_funct_1 @ X6)
% 0.34/0.62          | ~ (v1_relat_1 @ X6))),
% 0.34/0.62      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.34/0.62  thf(t48_funct_1, axiom,
% 0.34/0.62    (![A:$i]:
% 0.34/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.62       ( ![B:$i]:
% 0.34/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.62           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.34/0.62               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.34/0.62             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.34/0.62  thf('145', plain,
% 0.34/0.62      (![X3 : $i, X4 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ X3)
% 0.34/0.62          | ~ (v1_funct_1 @ X3)
% 0.34/0.62          | (v2_funct_1 @ X3)
% 0.34/0.62          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.34/0.62          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.34/0.62          | ~ (v1_funct_1 @ X4)
% 0.34/0.62          | ~ (v1_relat_1 @ X4))),
% 0.34/0.62      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.34/0.62  thf('146', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.34/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['144', '145'])).
% 0.34/0.62  thf(fc4_funct_1, axiom,
% 0.34/0.62    (![A:$i]:
% 0.34/0.62     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.34/0.62       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.34/0.62  thf('147', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.34/0.62      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.34/0.62  thf('148', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.34/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.34/0.62      inference('demod', [status(thm)], ['146', '147'])).
% 0.34/0.62  thf('149', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('simplify', [status(thm)], ['148'])).
% 0.34/0.62  thf('150', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.34/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['143', '149'])).
% 0.34/0.62  thf('151', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('simplify', [status(thm)], ['150'])).
% 0.34/0.62  thf('152', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.34/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['142', '151'])).
% 0.34/0.62  thf('153', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('simplify', [status(thm)], ['152'])).
% 0.34/0.62  thf('154', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['141', '153'])).
% 0.34/0.62  thf('155', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('simplify', [status(thm)], ['154'])).
% 0.34/0.62  thf('156', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.34/0.62      inference('simplify', [status(thm)], ['127'])).
% 0.34/0.62  thf('157', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.34/0.62  thf('158', plain,
% 0.34/0.62      (![X7 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X7)
% 0.34/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.34/0.62          | ~ (v1_funct_1 @ X7)
% 0.34/0.62          | ~ (v1_relat_1 @ X7))),
% 0.34/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.34/0.62  thf('159', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('simplify', [status(thm)], ['154'])).
% 0.34/0.62  thf('160', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.34/0.62  thf('161', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.34/0.62  thf('162', plain,
% 0.34/0.62      (![X7 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X7)
% 0.34/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.34/0.62          | ~ (v1_funct_1 @ X7)
% 0.34/0.62          | ~ (v1_relat_1 @ X7))),
% 0.34/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.34/0.62  thf('163', plain,
% 0.34/0.62      (![X6 : $i]:
% 0.34/0.62         (~ (v2_funct_1 @ X6)
% 0.34/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.34/0.62              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.34/0.62          | ~ (v1_funct_1 @ X6)
% 0.34/0.62          | ~ (v1_relat_1 @ X6))),
% 0.34/0.62      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.34/0.62  thf('164', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.34/0.62            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.34/0.62      inference('sup+', [status(thm)], ['162', '163'])).
% 0.34/0.62  thf('165', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.34/0.62              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.34/0.62      inference('sup-', [status(thm)], ['161', '164'])).
% 0.34/0.62  thf('166', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.34/0.62            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('simplify', [status(thm)], ['165'])).
% 0.34/0.62  thf('167', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.34/0.62              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.34/0.62      inference('sup-', [status(thm)], ['160', '166'])).
% 0.34/0.62  thf('168', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.34/0.62            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('simplify', [status(thm)], ['167'])).
% 0.34/0.62  thf('169', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.34/0.62              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.34/0.62      inference('sup-', [status(thm)], ['159', '168'])).
% 0.34/0.62  thf('170', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.34/0.62            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('simplify', [status(thm)], ['169'])).
% 0.34/0.62  thf('171', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.34/0.62            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.34/0.62      inference('sup+', [status(thm)], ['158', '170'])).
% 0.34/0.62  thf('172', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0)
% 0.34/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.34/0.62              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.34/0.62      inference('sup-', [status(thm)], ['157', '171'])).
% 0.34/0.62  thf('173', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.34/0.62            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.34/0.62          | ~ (v2_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_relat_1 @ X0))),
% 0.34/0.62      inference('simplify', [status(thm)], ['172'])).
% 0.34/0.62  thf('174', plain,
% 0.34/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.34/0.62        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.34/0.62            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.34/0.62      inference('sup-', [status(thm)], ['156', '173'])).
% 0.34/0.62  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('177', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('178', plain,
% 0.34/0.62      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.34/0.62            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.34/0.62      inference('demod', [status(thm)], ['174', '175', '176', '177'])).
% 0.34/0.62  thf('179', plain,
% 0.34/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.34/0.62        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.34/0.62            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.34/0.62      inference('sup-', [status(thm)], ['155', '178'])).
% 0.34/0.62  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('183', plain,
% 0.34/0.62      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.34/0.62         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.34/0.62      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 0.34/0.62  thf('184', plain,
% 0.34/0.62      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.34/0.62          = (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.34/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.34/0.62      inference('sup+', [status(thm)], ['140', '183'])).
% 0.34/0.62  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('187', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('188', plain,
% 0.34/0.62      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.34/0.62         = (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.34/0.62      inference('demod', [status(thm)], ['184', '185', '186', '187'])).
% 0.34/0.62  thf('189', plain,
% 0.34/0.62      (![X3 : $i, X4 : $i]:
% 0.34/0.62         (~ (v1_relat_1 @ X3)
% 0.34/0.62          | ~ (v1_funct_1 @ X3)
% 0.34/0.62          | (v2_funct_1 @ X3)
% 0.34/0.62          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.34/0.62          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.34/0.62          | ~ (v1_funct_1 @ X4)
% 0.34/0.62          | ~ (v1_relat_1 @ X4))),
% 0.34/0.62      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.34/0.62  thf('190', plain,
% 0.34/0.62      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.34/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.34/0.62        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['188', '189'])).
% 0.34/0.62  thf('191', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.34/0.62      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.34/0.62  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('194', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.34/0.62      inference('demod', [status(thm)], ['52', '53', '60'])).
% 0.34/0.62  thf('195', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.34/0.62      inference('simplify', [status(thm)], ['127'])).
% 0.34/0.62  thf('196', plain,
% 0.34/0.62      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.34/0.62        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.34/0.62      inference('demod', [status(thm)],
% 0.34/0.62                ['190', '191', '192', '193', '194', '195'])).
% 0.34/0.62  thf('197', plain,
% 0.34/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['139', '196'])).
% 0.34/0.62  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('200', plain,
% 0.34/0.62      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.34/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.34/0.62      inference('demod', [status(thm)], ['197', '198', '199'])).
% 0.34/0.62  thf('201', plain,
% 0.34/0.62      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.34/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.34/0.62        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['138', '200'])).
% 0.34/0.62  thf('202', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.34/0.62      inference('demod', [status(thm)], ['52', '53', '60'])).
% 0.34/0.62  thf('203', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('205', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('206', plain,
% 0.34/0.62      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.34/0.62        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.34/0.62      inference('demod', [status(thm)], ['201', '202', '203', '204', '205'])).
% 0.34/0.62  thf('207', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.34/0.62      inference('simplify', [status(thm)], ['206'])).
% 0.34/0.62  thf('208', plain,
% 0.34/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.34/0.62      inference('simplify', [status(thm)], ['116'])).
% 0.34/0.62  thf('209', plain,
% 0.34/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.34/0.62         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.34/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.34/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.34/0.62  thf('210', plain,
% 0.34/0.62      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['208', '209'])).
% 0.34/0.62  thf('211', plain,
% 0.34/0.62      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.34/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.34/0.62      inference('demod', [status(thm)], ['119', '128', '137', '207', '210'])).
% 0.34/0.62  thf('212', plain,
% 0.34/0.62      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.34/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.34/0.62        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.34/0.62      inference('sup-', [status(thm)], ['108', '211'])).
% 0.34/0.62  thf('213', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.34/0.62      inference('demod', [status(thm)], ['52', '53', '60'])).
% 0.34/0.62  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('216', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('217', plain,
% 0.34/0.62      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.34/0.62        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.34/0.62      inference('demod', [status(thm)], ['212', '213', '214', '215', '216'])).
% 0.34/0.62  thf('218', plain,
% 0.34/0.62      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.34/0.62         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.34/0.62      inference('simplify', [status(thm)], ['217'])).
% 0.34/0.62  thf('219', plain,
% 0.34/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.34/0.62          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.34/0.62      inference('demod', [status(thm)], ['107', '218'])).
% 0.34/0.62  thf('220', plain,
% 0.34/0.62      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.34/0.62           sk_C)
% 0.34/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.34/0.62      inference('sup-', [status(thm)], ['0', '219'])).
% 0.34/0.62  thf('221', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.34/0.62  thf('222', plain,
% 0.34/0.62      ((m1_subset_1 @ sk_C @ 
% 0.34/0.62        (k1_zfmisc_1 @ 
% 0.34/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.34/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.34/0.62  thf(reflexivity_r2_funct_2, axiom,
% 0.34/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.34/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.34/0.62         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.34/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.34/0.62       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.34/0.62  thf('223', plain,
% 0.34/0.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.34/0.62         ((r2_funct_2 @ X22 @ X23 @ X24 @ X24)
% 0.34/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.34/0.62          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.34/0.62          | ~ (v1_funct_1 @ X24)
% 0.34/0.62          | ~ (v1_funct_1 @ X25)
% 0.34/0.62          | ~ (v1_funct_2 @ X25 @ X22 @ X23)
% 0.34/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.34/0.62      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.34/0.62  thf('224', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (m1_subset_1 @ X0 @ 
% 0.34/0.62             (k1_zfmisc_1 @ 
% 0.34/0.62              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.34/0.62          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.34/0.62          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.34/0.62             sk_C))),
% 0.34/0.62      inference('sup-', [status(thm)], ['222', '223'])).
% 0.34/0.62  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('226', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.34/0.62      inference('demod', [status(thm)], ['80', '81'])).
% 0.34/0.62  thf('227', plain,
% 0.34/0.62      (![X0 : $i]:
% 0.34/0.62         (~ (m1_subset_1 @ X0 @ 
% 0.34/0.62             (k1_zfmisc_1 @ 
% 0.34/0.62              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.34/0.62          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.34/0.62          | ~ (v1_funct_1 @ X0)
% 0.34/0.62          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.34/0.62             sk_C))),
% 0.34/0.62      inference('demod', [status(thm)], ['224', '225', '226'])).
% 0.34/0.62  thf('228', plain,
% 0.34/0.62      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.34/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.34/0.62      inference('sup-', [status(thm)], ['221', '227'])).
% 0.34/0.62  thf('229', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('230', plain,
% 0.34/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.34/0.62      inference('demod', [status(thm)], ['80', '81'])).
% 0.34/0.62  thf('231', plain,
% 0.34/0.62      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.34/0.62      inference('demod', [status(thm)], ['228', '229', '230'])).
% 0.34/0.62  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.62  thf('233', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('234', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.62  thf('235', plain, ($false),
% 0.34/0.62      inference('demod', [status(thm)], ['220', '231', '232', '233', '234'])).
% 0.34/0.62  
% 0.34/0.62  % SZS output end Refutation
% 0.34/0.62  
% 0.34/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
