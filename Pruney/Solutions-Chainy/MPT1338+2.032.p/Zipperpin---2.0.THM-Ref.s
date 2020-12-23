%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.88o2dO2jSg

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:52 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  210 (2474 expanded)
%              Number of leaves         :   38 ( 744 expanded)
%              Depth                    :   28
%              Number of atoms          : 1943 (65134 expanded)
%              Number of equality atoms :  135 (3370 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('9',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','23'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X23 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27','30'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','23'])).

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

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X20 @ X22 )
       != X20 )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k2_tops_2 @ X21 @ X20 @ X22 )
        = ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('38',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('44',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf('47',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('48',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('52',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','52'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('57',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','52'])).

thf('59',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != X13 )
      | ( v1_partfun1 @ X14 @ X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('67',plain,(
    ! [X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v4_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
      | ( v1_partfun1 @ X14 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','52'])).

thf('71',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('76',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','72','73','74','75'])).

thf('77',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['56','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('85',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('86',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','86'])).

thf('88',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['51'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('94',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','52'])).

thf('96',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('97',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('104',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','104'])).

thf('106',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('119',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['116','121'])).

thf('123',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X20 @ X22 )
       != X20 )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k2_tops_2 @ X21 @ X20 @ X22 )
        = ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','125','134','135'])).

thf('137',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('144',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('146',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','146'])).

thf('148',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('151',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('152',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['88'])).

thf('153',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','155'])).

thf('157',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','156'])).

thf('158',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('162',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('163',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','163'])).

thf('165',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','164'])).

thf('166',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['88'])).

thf('168',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['166','167'])).

thf('169',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['94','168'])).

thf('170',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.88o2dO2jSg
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 352 iterations in 0.081s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.36/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(t62_tops_2, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_struct_0 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                 ( m1_subset_1 @
% 0.36/0.54                   C @ 
% 0.36/0.54                   ( k1_zfmisc_1 @
% 0.36/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54               ( ( ( ( k2_relset_1 @
% 0.36/0.54                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.54                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.54                   ( v2_funct_1 @ C ) ) =>
% 0.36/0.54                 ( ( ( k1_relset_1 @
% 0.36/0.54                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.54                       ( k2_tops_2 @
% 0.36/0.54                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.54                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.54                   ( ( k2_relset_1 @
% 0.36/0.54                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.54                       ( k2_tops_2 @
% 0.36/0.54                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.54                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( l1_struct_0 @ A ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.36/0.54              ( ![C:$i]:
% 0.36/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                    ( v1_funct_2 @
% 0.36/0.54                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                    ( m1_subset_1 @
% 0.36/0.54                      C @ 
% 0.36/0.54                      ( k1_zfmisc_1 @
% 0.36/0.54                        ( k2_zfmisc_1 @
% 0.36/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54                  ( ( ( ( k2_relset_1 @
% 0.36/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.54                        ( k2_struct_0 @ B ) ) & 
% 0.36/0.54                      ( v2_funct_1 @ C ) ) =>
% 0.36/0.54                    ( ( ( k1_relset_1 @
% 0.36/0.54                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.54                          ( k2_tops_2 @
% 0.36/0.54                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.54                        ( k2_struct_0 @ B ) ) & 
% 0.36/0.54                      ( ( k2_relset_1 @
% 0.36/0.54                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.54                          ( k2_tops_2 @
% 0.36/0.54                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.54                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t132_funct_2, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.54           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.36/0.54           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.54         (((X15) = (k1_xboole_0))
% 0.36/0.54          | ~ (v1_funct_1 @ X16)
% 0.36/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.36/0.54          | (v1_partfun1 @ X16 @ X17)
% 0.36/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.36/0.54          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.36/0.54          | ~ (v1_funct_1 @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.54         (~ (v1_funct_2 @ X16 @ X17 @ X15)
% 0.36/0.54          | (v1_partfun1 @ X16 @ X17)
% 0.36/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 0.36/0.54          | ~ (v1_funct_1 @ X16)
% 0.36/0.54          | ((X15) = (k1_xboole_0)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.36/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.54        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.36/0.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.36/0.54  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.36/0.54        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.36/0.54  thf(d4_partfun1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.36/0.54       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         (~ (v1_partfun1 @ X14 @ X13)
% 0.36/0.54          | ((k1_relat_1 @ X14) = (X13))
% 0.36/0.54          | ~ (v4_relat_1 @ X14 @ X13)
% 0.36/0.54          | ~ (v1_relat_1 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.54        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.36/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc1_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( v1_relat_1 @ C ) ))).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((v1_relat_1 @ X1)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.54  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc2_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         ((v4_relat_1 @ X4 @ X5)
% 0.36/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.54  thf('15', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.36/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.36/0.54  thf(fc2_struct_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X19 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.36/0.54          | ~ (l1_struct_0 @ X19)
% 0.36/0.54          | (v2_struct_0 @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.36/0.54        | (v2_struct_0 @ sk_B)
% 0.36/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.54  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.36/0.54  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('23', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '23'])).
% 0.36/0.54  thf(dt_k2_tops_2, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.36/0.54         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.36/0.54         ( m1_subset_1 @
% 0.36/0.54           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.36/0.54           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.54         ((m1_subset_1 @ (k2_tops_2 @ X23 @ X24 @ X25) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.36/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.36/0.54          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.36/0.54          | ~ (v1_funct_1 @ X25))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.54        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.54        | (m1_subset_1 @ 
% 0.36/0.54           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.54           (k1_zfmisc_1 @ 
% 0.36/0.54            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('29', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      ((m1_subset_1 @ 
% 0.36/0.54        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['26', '27', '30'])).
% 0.36/0.54  thf(d3_struct_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '23'])).
% 0.36/0.54  thf(d4_tops_2, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.54         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.54         (((k2_relset_1 @ X21 @ X20 @ X22) != (X20))
% 0.36/0.54          | ~ (v2_funct_1 @ X22)
% 0.36/0.54          | ((k2_tops_2 @ X21 @ X20 @ X22) = (k2_funct_1 @ X22))
% 0.36/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.36/0.54          | ~ (v1_funct_2 @ X22 @ X21 @ X20)
% 0.36/0.54          | ~ (v1_funct_1 @ X22))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.54        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.54        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54            = (k2_funct_1 @ sk_C))
% 0.36/0.54        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.54        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54            != (u1_struct_0 @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.54  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.54  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54          = (k2_funct_1 @ sk_C))
% 0.36/0.54        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54            != (u1_struct_0 @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.54         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.36/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54         = (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf('43', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54         = (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54          = (k2_funct_1 @ sk_C))
% 0.36/0.54        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['39', '44'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.36/0.54        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.54        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54            = (k2_funct_1 @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['32', '45'])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54         = (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54         = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('49', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.54  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.54        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54            = (k2_funct_1 @ sk_C)))),
% 0.36/0.54      inference('demod', [status(thm)], ['46', '49', '50'])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54         = (k2_funct_1 @ sk_C))),
% 0.36/0.54      inference('simplify', [status(thm)], ['51'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['31', '52'])).
% 0.36/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.54  thf('54', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.54         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.36/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.54         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.54  thf(t55_funct_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.54       ( ( v2_funct_1 @ A ) =>
% 0.36/0.54         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.36/0.54           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.36/0.54  thf('56', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X0)
% 0.36/0.54          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.54  thf('57', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['31', '52'])).
% 0.36/0.54  thf('59', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         ((v4_relat_1 @ X4 @ X5)
% 0.36/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.54  thf('60', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.54  thf('61', plain,
% 0.36/0.54      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.36/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['57', '60'])).
% 0.36/0.54  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.54  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('64', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X0)
% 0.36/0.54          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         (((k1_relat_1 @ X14) != (X13))
% 0.36/0.54          | (v1_partfun1 @ X14 @ X13)
% 0.36/0.54          | ~ (v4_relat_1 @ X14 @ X13)
% 0.36/0.54          | ~ (v1_relat_1 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.36/0.54  thf('67', plain,
% 0.36/0.54      (![X14 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X14)
% 0.36/0.54          | ~ (v4_relat_1 @ X14 @ (k1_relat_1 @ X14))
% 0.36/0.54          | (v1_partfun1 @ X14 @ (k1_relat_1 @ X14)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['66'])).
% 0.36/0.54  thf('68', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v2_funct_1 @ X0)
% 0.36/0.54          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.54          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['65', '67'])).
% 0.36/0.54  thf('69', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.54        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.54           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.54        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['64', '68'])).
% 0.36/0.54  thf('70', plain,
% 0.36/0.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['31', '52'])).
% 0.36/0.54  thf('71', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((v1_relat_1 @ X1)
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.54  thf('72', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.54  thf('73', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf('76', plain,
% 0.36/0.54      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.54      inference('demod', [status(thm)], ['69', '72', '73', '74', '75'])).
% 0.36/0.54  thf('77', plain,
% 0.36/0.54      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.54        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.54      inference('sup+', [status(thm)], ['56', '76'])).
% 0.36/0.54  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('81', plain, ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.36/0.54  thf('82', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         (~ (v1_partfun1 @ X14 @ X13)
% 0.36/0.54          | ((k1_relat_1 @ X14) = (X13))
% 0.36/0.54          | ~ (v4_relat_1 @ X14 @ X13)
% 0.36/0.54          | ~ (v1_relat_1 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.36/0.54  thf('83', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.54        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.36/0.54        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['81', '82'])).
% 0.36/0.54  thf('84', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.54  thf('85', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.36/0.54  thf('86', plain,
% 0.36/0.54      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.36/0.54  thf('87', plain,
% 0.36/0.54      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.54         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['55', '86'])).
% 0.36/0.54  thf('88', plain,
% 0.36/0.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54          != (k2_struct_0 @ sk_B))
% 0.36/0.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54            != (k2_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('89', plain,
% 0.36/0.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54          != (k2_struct_0 @ sk_B)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_B))))),
% 0.36/0.54      inference('split', [status(esa)], ['88'])).
% 0.36/0.54  thf('90', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('91', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('92', plain,
% 0.36/0.54      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54         = (k2_funct_1 @ sk_C))),
% 0.36/0.54      inference('simplify', [status(thm)], ['51'])).
% 0.36/0.54  thf('93', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.54  thf('94', plain,
% 0.36/0.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.54          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_B))))),
% 0.36/0.54      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.36/0.54  thf('95', plain,
% 0.36/0.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['31', '52'])).
% 0.36/0.54  thf('96', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.54         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.36/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.54  thf('97', plain,
% 0.36/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.54         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.36/0.54  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('99', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X0)
% 0.36/0.54          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.54          | ~ (v1_funct_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.54  thf('100', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.54        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.54        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['98', '99'])).
% 0.36/0.54  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('102', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.54        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['100', '101'])).
% 0.36/0.54  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf('104', plain,
% 0.36/0.54      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.54      inference('demod', [status(thm)], ['102', '103'])).
% 0.36/0.54  thf('105', plain,
% 0.36/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.54         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['97', '104'])).
% 0.36/0.54  thf('106', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.54  thf('107', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.54  thf('108', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('109', plain,
% 0.36/0.54      (((m1_subset_1 @ sk_C @ 
% 0.36/0.54         (k1_zfmisc_1 @ 
% 0.36/0.54          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.36/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['107', '108'])).
% 0.36/0.54  thf('110', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('111', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.54      inference('demod', [status(thm)], ['109', '110'])).
% 0.36/0.54  thf('112', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.54  thf('113', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['111', '112'])).
% 0.36/0.54  thf('114', plain,
% 0.36/0.54      (((m1_subset_1 @ sk_C @ 
% 0.36/0.54         (k1_zfmisc_1 @ 
% 0.36/0.54          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))
% 0.36/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['106', '113'])).
% 0.36/0.54  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('116', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['114', '115'])).
% 0.36/0.54  thf('117', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.54  thf('118', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('119', plain,
% 0.36/0.54      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['117', '118'])).
% 0.36/0.54  thf('120', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('121', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['119', '120'])).
% 0.36/0.54  thf('122', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['116', '121'])).
% 0.36/0.54  thf('123', plain,
% 0.36/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.54         (((k2_relset_1 @ X21 @ X20 @ X22) != (X20))
% 0.36/0.54          | ~ (v2_funct_1 @ X22)
% 0.36/0.54          | ((k2_tops_2 @ X21 @ X20 @ X22) = (k2_funct_1 @ X22))
% 0.36/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.36/0.54          | ~ (v1_funct_2 @ X22 @ X21 @ X20)
% 0.36/0.54          | ~ (v1_funct_1 @ X22))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.54  thf('124', plain,
% 0.36/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.54        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.36/0.54        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.54            = (k2_funct_1 @ sk_C))
% 0.36/0.54        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.54        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.54            != (k2_relat_1 @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['122', '123'])).
% 0.36/0.54  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('126', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.54  thf('127', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('128', plain,
% 0.36/0.54      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['126', '127'])).
% 0.36/0.54  thf('129', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('130', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['128', '129'])).
% 0.36/0.54  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.54  thf('132', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['130', '131'])).
% 0.36/0.54  thf('133', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('134', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['132', '133'])).
% 0.36/0.54  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('136', plain,
% 0.36/0.54      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.54          = (k2_funct_1 @ sk_C))
% 0.36/0.54        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.54            != (k2_relat_1 @ sk_C)))),
% 0.36/0.54      inference('demod', [status(thm)], ['124', '125', '134', '135'])).
% 0.36/0.54  thf('137', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.54  thf('138', plain,
% 0.36/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54         = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('139', plain,
% 0.36/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54          = (k2_struct_0 @ sk_B))
% 0.36/0.54        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['137', '138'])).
% 0.36/0.54  thf('140', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('141', plain,
% 0.36/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.54         = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['139', '140'])).
% 0.36/0.54  thf('142', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.54  thf('143', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.54  thf('144', plain,
% 0.36/0.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.54         = (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.36/0.54  thf('145', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('146', plain,
% 0.36/0.54      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.54         = (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['144', '145'])).
% 0.36/0.54  thf('147', plain,
% 0.36/0.54      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.54          = (k2_funct_1 @ sk_C))
% 0.36/0.54        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.54      inference('demod', [status(thm)], ['136', '146'])).
% 0.36/0.54  thf('148', plain,
% 0.36/0.54      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.54         = (k2_funct_1 @ sk_C))),
% 0.36/0.54      inference('simplify', [status(thm)], ['147'])).
% 0.36/0.54  thf('149', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.54  thf('150', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.54  thf('151', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.54  thf('152', plain,
% 0.36/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54          != (k2_struct_0 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_A))))),
% 0.36/0.54      inference('split', [status(esa)], ['88'])).
% 0.36/0.54  thf('153', plain,
% 0.36/0.54      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54           != (k2_struct_0 @ sk_A))
% 0.36/0.54         | ~ (l1_struct_0 @ sk_B)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['151', '152'])).
% 0.36/0.54  thf('154', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('155', plain,
% 0.36/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54          != (k2_struct_0 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['153', '154'])).
% 0.36/0.54  thf('156', plain,
% 0.36/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.36/0.54          != (k2_struct_0 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['150', '155'])).
% 0.36/0.54  thf('157', plain,
% 0.36/0.54      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.36/0.54           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.36/0.54           != (k2_struct_0 @ sk_A))
% 0.36/0.54         | ~ (l1_struct_0 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['149', '156'])).
% 0.36/0.54  thf('158', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('159', plain,
% 0.36/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.36/0.54          != (k2_struct_0 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['157', '158'])).
% 0.36/0.54  thf('160', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['119', '120'])).
% 0.36/0.54  thf('161', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('162', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['119', '120'])).
% 0.36/0.54  thf('163', plain,
% 0.36/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.54          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.36/0.54          != (k1_relat_1 @ sk_C)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 0.36/0.54  thf('164', plain,
% 0.36/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.54          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['148', '163'])).
% 0.36/0.54  thf('165', plain,
% 0.36/0.54      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54                = (k2_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['105', '164'])).
% 0.36/0.54  thf('166', plain,
% 0.36/0.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54          = (k2_struct_0 @ sk_A)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['165'])).
% 0.36/0.54  thf('167', plain,
% 0.36/0.54      (~
% 0.36/0.54       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54          = (k2_struct_0 @ sk_B))) | 
% 0.36/0.54       ~
% 0.36/0.54       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54          = (k2_struct_0 @ sk_A)))),
% 0.36/0.54      inference('split', [status(esa)], ['88'])).
% 0.36/0.54  thf('168', plain,
% 0.36/0.54      (~
% 0.36/0.54       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.54          = (k2_struct_0 @ sk_B)))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['166', '167'])).
% 0.36/0.54  thf('169', plain,
% 0.36/0.54      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.54         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['94', '168'])).
% 0.36/0.54  thf('170', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['87', '169'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
