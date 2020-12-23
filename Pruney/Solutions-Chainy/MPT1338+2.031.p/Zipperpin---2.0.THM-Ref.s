%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oL5GM9TyYs

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:52 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  215 (4477 expanded)
%              Number of leaves         :   42 (1410 expanded)
%              Depth                    :   38
%              Number of atoms          : 2003 (114436 expanded)
%              Number of equality atoms :  149 (6514 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

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

thf('1',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_partfun1 @ X20 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X20 @ X18 @ X19 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('6',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9','10','11','12'])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('16',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('22',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('23',plain,(
    ! [X16: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 )
      | ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['25','28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','32','35','36','37'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('48',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('53',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('55',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X23 @ X25 )
       != X23 )
      | ~ ( v2_funct_1 @ X25 )
      | ( ( k2_tops_2 @ X24 @ X23 @ X25 )
        = ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('61',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('63',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','51','52','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('71',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X26 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('77',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('78',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('79',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('80',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('81',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('83',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('85',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != X14 )
      | ( v1_partfun1 @ X15 @ X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('93',plain,(
    ! [X15: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v4_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
      | ( v1_partfun1 @ X15 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('97',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('98',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('102',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','98','99','100','101'])).

thf('103',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['82','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('111',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('112',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','112'])).

thf('114',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X23 @ X25 )
       != X23 )
      | ~ ( v2_funct_1 @ X25 )
      | ( ( k2_tops_2 @ X24 @ X23 @ X25 )
        = ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('133',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('138',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('139',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','130','131','139'])).

thf('141',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('143',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('145',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('146',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','148'])).

thf('150',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('154',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','154'])).

thf('156',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','155'])).

thf('157',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('159',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['157','158'])).

thf('160',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['69','159'])).

thf('161',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('162',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('163',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['160','163'])).

thf('165',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','164'])).

thf('166',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','166','167','168','169'])).

thf('171',plain,(
    $false ),
    inference(simplify,[status(thm)],['170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oL5GM9TyYs
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.59/1.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.59/1.80  % Solved by: fo/fo7.sh
% 1.59/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.59/1.80  % done 769 iterations in 1.349s
% 1.59/1.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.59/1.80  % SZS output start Refutation
% 1.59/1.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.59/1.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.59/1.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.59/1.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.59/1.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.59/1.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.59/1.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.59/1.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.59/1.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.59/1.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.59/1.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.59/1.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.59/1.80  thf(sk_B_type, type, sk_B: $i).
% 1.59/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.59/1.80  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.59/1.80  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.59/1.80  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.59/1.80  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.59/1.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.59/1.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.59/1.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.59/1.80  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.59/1.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.59/1.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.59/1.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.59/1.80  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.59/1.80  thf(sk_C_type, type, sk_C: $i).
% 1.59/1.80  thf(t55_funct_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.59/1.80       ( ( v2_funct_1 @ A ) =>
% 1.59/1.80         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.59/1.80           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.59/1.80  thf('0', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.80  thf(t62_tops_2, conjecture,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( l1_struct_0 @ A ) =>
% 1.59/1.80       ( ![B:$i]:
% 1.59/1.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.59/1.80           ( ![C:$i]:
% 1.59/1.80             ( ( ( v1_funct_1 @ C ) & 
% 1.59/1.80                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.59/1.80                 ( m1_subset_1 @
% 1.59/1.80                   C @ 
% 1.59/1.80                   ( k1_zfmisc_1 @
% 1.59/1.80                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.59/1.80               ( ( ( ( k2_relset_1 @
% 1.59/1.80                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.59/1.80                     ( k2_struct_0 @ B ) ) & 
% 1.59/1.80                   ( v2_funct_1 @ C ) ) =>
% 1.59/1.80                 ( ( ( k1_relset_1 @
% 1.59/1.80                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.59/1.80                       ( k2_tops_2 @
% 1.59/1.80                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.59/1.80                     ( k2_struct_0 @ B ) ) & 
% 1.59/1.80                   ( ( k2_relset_1 @
% 1.59/1.80                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.59/1.80                       ( k2_tops_2 @
% 1.59/1.80                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.59/1.80                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.59/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.59/1.80    (~( ![A:$i]:
% 1.59/1.80        ( ( l1_struct_0 @ A ) =>
% 1.59/1.80          ( ![B:$i]:
% 1.59/1.80            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.59/1.80              ( ![C:$i]:
% 1.59/1.80                ( ( ( v1_funct_1 @ C ) & 
% 1.59/1.80                    ( v1_funct_2 @
% 1.59/1.80                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.59/1.80                    ( m1_subset_1 @
% 1.59/1.80                      C @ 
% 1.59/1.80                      ( k1_zfmisc_1 @
% 1.59/1.80                        ( k2_zfmisc_1 @
% 1.59/1.80                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.59/1.80                  ( ( ( ( k2_relset_1 @
% 1.59/1.80                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.59/1.80                        ( k2_struct_0 @ B ) ) & 
% 1.59/1.80                      ( v2_funct_1 @ C ) ) =>
% 1.59/1.80                    ( ( ( k1_relset_1 @
% 1.59/1.80                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.59/1.80                          ( k2_tops_2 @
% 1.59/1.80                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.59/1.80                        ( k2_struct_0 @ B ) ) & 
% 1.59/1.80                      ( ( k2_relset_1 @
% 1.59/1.80                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.59/1.80                          ( k2_tops_2 @
% 1.59/1.80                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.59/1.80                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.59/1.80    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.59/1.80  thf('1', plain,
% 1.59/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80          != (k2_struct_0 @ sk_B))
% 1.59/1.80        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80            != (k2_struct_0 @ sk_A)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('2', plain,
% 1.59/1.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80          != (k2_struct_0 @ sk_A)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_A))))),
% 1.59/1.80      inference('split', [status(esa)], ['1'])).
% 1.59/1.80  thf(d3_struct_0, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.59/1.80  thf('3', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.59/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.80  thf('4', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(t35_funct_2, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.59/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.80       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.59/1.80         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.59/1.80           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.59/1.80             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.59/1.80  thf('5', plain,
% 1.59/1.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.59/1.80         (((X18) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_funct_1 @ X19)
% 1.59/1.80          | ~ (v1_funct_2 @ X19 @ X20 @ X18)
% 1.59/1.80          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 1.59/1.80          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19)) = (k6_partfun1 @ X20))
% 1.59/1.80          | ~ (v2_funct_1 @ X19)
% 1.59/1.80          | ((k2_relset_1 @ X20 @ X18 @ X19) != (X18)))),
% 1.59/1.80      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.59/1.80  thf('6', plain,
% 1.59/1.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80          != (u1_struct_0 @ sk_B))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C)
% 1.59/1.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.59/1.80            = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.80        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['4', '5'])).
% 1.59/1.80  thf('7', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(redefinition_k2_relset_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.80       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.59/1.80  thf('8', plain,
% 1.59/1.80      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.59/1.80         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.59/1.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.59/1.80  thf('9', plain,
% 1.59/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80         = (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['7', '8'])).
% 1.59/1.80  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('11', plain,
% 1.59/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('13', plain,
% 1.59/1.80      ((((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B))
% 1.59/1.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.59/1.80            = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.80        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.59/1.80      inference('demod', [status(thm)], ['6', '9', '10', '11', '12'])).
% 1.59/1.80  thf('14', plain,
% 1.59/1.80      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.59/1.80        | ~ (l1_struct_0 @ sk_B)
% 1.59/1.80        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.59/1.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.59/1.80            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['3', '13'])).
% 1.59/1.80  thf('15', plain,
% 1.59/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80         = (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['7', '8'])).
% 1.59/1.80  thf('16', plain,
% 1.59/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80         = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('17', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.59/1.80  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('19', plain,
% 1.59/1.80      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.59/1.80        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.59/1.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.59/1.80            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 1.59/1.80      inference('demod', [status(thm)], ['14', '17', '18'])).
% 1.59/1.80  thf('20', plain,
% 1.59/1.80      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.59/1.80          = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.80        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.59/1.80      inference('simplify', [status(thm)], ['19'])).
% 1.59/1.80  thf(t58_funct_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.59/1.80       ( ( v2_funct_1 @ A ) =>
% 1.59/1.80         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.59/1.80             ( k1_relat_1 @ A ) ) & 
% 1.59/1.80           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.59/1.80             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.59/1.80  thf('21', plain,
% 1.59/1.80      (![X1 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X1)
% 1.59/1.80          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X1)))
% 1.59/1.80              = (k1_relat_1 @ X1))
% 1.59/1.80          | ~ (v1_funct_1 @ X1)
% 1.59/1.80          | ~ (v1_relat_1 @ X1))),
% 1.59/1.80      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.59/1.80  thf('22', plain,
% 1.59/1.80      ((((k1_relat_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.80          = (k1_relat_1 @ sk_C))
% 1.59/1.80        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.59/1.80        | ~ (v1_relat_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup+', [status(thm)], ['20', '21'])).
% 1.59/1.80  thf(dt_k6_partfun1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( m1_subset_1 @
% 1.59/1.80         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.59/1.80       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.59/1.80  thf('23', plain, (![X16 : $i]: (v1_partfun1 @ (k6_partfun1 @ X16) @ X16)),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.59/1.80  thf(d4_partfun1, axiom,
% 1.59/1.80    (![A:$i,B:$i]:
% 1.59/1.80     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.59/1.80       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.59/1.80  thf('24', plain,
% 1.59/1.80      (![X14 : $i, X15 : $i]:
% 1.59/1.80         (~ (v1_partfun1 @ X15 @ X14)
% 1.59/1.80          | ((k1_relat_1 @ X15) = (X14))
% 1.59/1.80          | ~ (v4_relat_1 @ X15 @ X14)
% 1.59/1.80          | ~ (v1_relat_1 @ X15))),
% 1.59/1.80      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.59/1.80  thf('25', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.59/1.80          | ~ (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)
% 1.59/1.80          | ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['23', '24'])).
% 1.59/1.80  thf('26', plain,
% 1.59/1.80      (![X17 : $i]:
% 1.59/1.80         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 1.59/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.59/1.80  thf(cc1_relset_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.80       ( v1_relat_1 @ C ) ))).
% 1.59/1.80  thf('27', plain,
% 1.59/1.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.59/1.80         ((v1_relat_1 @ X2)
% 1.59/1.80          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.59/1.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.59/1.80  thf('28', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.59/1.80      inference('sup-', [status(thm)], ['26', '27'])).
% 1.59/1.80  thf('29', plain,
% 1.59/1.80      (![X17 : $i]:
% 1.59/1.80         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 1.59/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.59/1.80  thf(cc2_relset_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.59/1.80  thf('30', plain,
% 1.59/1.80      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.59/1.80         ((v4_relat_1 @ X5 @ X6)
% 1.59/1.80          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.59/1.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.59/1.80  thf('31', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 1.59/1.80      inference('sup-', [status(thm)], ['29', '30'])).
% 1.59/1.80  thf('32', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.59/1.80      inference('demod', [status(thm)], ['25', '28', '31'])).
% 1.59/1.80  thf('33', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('34', plain,
% 1.59/1.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.59/1.80         ((v1_relat_1 @ X2)
% 1.59/1.80          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.59/1.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.59/1.80  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('sup-', [status(thm)], ['33', '34'])).
% 1.59/1.80  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('38', plain,
% 1.59/1.80      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 1.59/1.80        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.59/1.80      inference('demod', [status(thm)], ['22', '32', '35', '36', '37'])).
% 1.59/1.80  thf(fc2_struct_0, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.59/1.80       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.59/1.80  thf('39', plain,
% 1.59/1.80      (![X22 : $i]:
% 1.59/1.80         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 1.59/1.80          | ~ (l1_struct_0 @ X22)
% 1.59/1.80          | (v2_struct_0 @ X22))),
% 1.59/1.80      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.59/1.80  thf('40', plain,
% 1.59/1.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.59/1.80        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 1.59/1.80        | (v2_struct_0 @ sk_B)
% 1.59/1.80        | ~ (l1_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup-', [status(thm)], ['38', '39'])).
% 1.59/1.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.59/1.80  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.59/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.59/1.80  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('43', plain,
% 1.59/1.80      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.59/1.80      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.59/1.80  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('45', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.59/1.80      inference('clc', [status(thm)], ['43', '44'])).
% 1.59/1.80  thf('46', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.59/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.80  thf('47', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.59/1.80      inference('clc', [status(thm)], ['43', '44'])).
% 1.59/1.80  thf('48', plain,
% 1.59/1.80      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 1.59/1.80      inference('sup+', [status(thm)], ['46', '47'])).
% 1.59/1.80  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('50', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['48', '49'])).
% 1.59/1.80  thf('51', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['45', '50'])).
% 1.59/1.80  thf('52', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['45', '50'])).
% 1.59/1.80  thf('53', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.59/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.80  thf('54', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(d4_tops_2, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.59/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.80       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.59/1.80         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.59/1.80  thf('55', plain,
% 1.59/1.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.59/1.80         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 1.59/1.80          | ~ (v2_funct_1 @ X25)
% 1.59/1.80          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 1.59/1.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.59/1.80          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 1.59/1.80          | ~ (v1_funct_1 @ X25))),
% 1.59/1.80      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.59/1.80  thf('56', plain,
% 1.59/1.80      ((~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.59/1.80        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80            = (k2_funct_1 @ sk_C))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C)
% 1.59/1.80        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80            != (u1_struct_0 @ sk_B)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['54', '55'])).
% 1.59/1.80  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('58', plain,
% 1.59/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('60', plain,
% 1.59/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80         = (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['7', '8'])).
% 1.59/1.80  thf('61', plain,
% 1.59/1.80      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80          = (k2_funct_1 @ sk_C))
% 1.59/1.80        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.59/1.80      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 1.59/1.80  thf('62', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['45', '50'])).
% 1.59/1.80  thf('63', plain,
% 1.59/1.80      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80          = (k2_funct_1 @ sk_C))
% 1.59/1.80        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.59/1.80      inference('demod', [status(thm)], ['61', '62'])).
% 1.59/1.80  thf('64', plain,
% 1.59/1.80      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.59/1.80        | ~ (l1_struct_0 @ sk_B)
% 1.59/1.80        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80            = (k2_funct_1 @ sk_C)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['53', '63'])).
% 1.59/1.80  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.59/1.80  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('67', plain,
% 1.59/1.80      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.59/1.80        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80            = (k2_funct_1 @ sk_C)))),
% 1.59/1.80      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.59/1.80  thf('68', plain,
% 1.59/1.80      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80         = (k2_funct_1 @ sk_C))),
% 1.59/1.80      inference('simplify', [status(thm)], ['67'])).
% 1.59/1.80  thf('69', plain,
% 1.59/1.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_A))))),
% 1.59/1.80      inference('demod', [status(thm)], ['2', '51', '52', '68'])).
% 1.59/1.80  thf('70', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(dt_k2_tops_2, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.59/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.80       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 1.59/1.80         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 1.59/1.80         ( m1_subset_1 @
% 1.59/1.80           ( k2_tops_2 @ A @ B @ C ) @ 
% 1.59/1.80           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 1.59/1.80  thf('71', plain,
% 1.59/1.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.59/1.80         ((m1_subset_1 @ (k2_tops_2 @ X26 @ X27 @ X28) @ 
% 1.59/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 1.59/1.80          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.59/1.80          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.59/1.80          | ~ (v1_funct_1 @ X28))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.59/1.80  thf('72', plain,
% 1.59/1.80      ((~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.59/1.80        | (m1_subset_1 @ 
% 1.59/1.80           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.59/1.80           (k1_zfmisc_1 @ 
% 1.59/1.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['70', '71'])).
% 1.59/1.80  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('74', plain,
% 1.59/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('75', plain,
% 1.59/1.80      ((m1_subset_1 @ 
% 1.59/1.80        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.59/1.80      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.59/1.80  thf('76', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['45', '50'])).
% 1.59/1.80  thf('77', plain,
% 1.59/1.80      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80         = (k2_funct_1 @ sk_C))),
% 1.59/1.80      inference('simplify', [status(thm)], ['67'])).
% 1.59/1.80  thf('78', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['45', '50'])).
% 1.59/1.80  thf('79', plain,
% 1.59/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 1.59/1.80      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 1.59/1.80  thf(redefinition_k1_relset_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.59/1.80  thf('80', plain,
% 1.59/1.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.59/1.80         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.59/1.80          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.59/1.80  thf('81', plain,
% 1.59/1.80      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['79', '80'])).
% 1.59/1.80  thf('82', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.80  thf('83', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.59/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.80  thf('84', plain,
% 1.59/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 1.59/1.80      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 1.59/1.80  thf('85', plain,
% 1.59/1.80      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.59/1.80         ((v4_relat_1 @ X5 @ X6)
% 1.59/1.80          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.59/1.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.59/1.80  thf('86', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup-', [status(thm)], ['84', '85'])).
% 1.59/1.80  thf('87', plain,
% 1.59/1.80      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 1.59/1.80        | ~ (l1_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['83', '86'])).
% 1.59/1.80  thf('88', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.59/1.80  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('90', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.59/1.80  thf('91', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.80  thf('92', plain,
% 1.59/1.80      (![X14 : $i, X15 : $i]:
% 1.59/1.80         (((k1_relat_1 @ X15) != (X14))
% 1.59/1.80          | (v1_partfun1 @ X15 @ X14)
% 1.59/1.80          | ~ (v4_relat_1 @ X15 @ X14)
% 1.59/1.80          | ~ (v1_relat_1 @ X15))),
% 1.59/1.80      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.59/1.80  thf('93', plain,
% 1.59/1.80      (![X15 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X15)
% 1.59/1.80          | ~ (v4_relat_1 @ X15 @ (k1_relat_1 @ X15))
% 1.59/1.80          | (v1_partfun1 @ X15 @ (k1_relat_1 @ X15)))),
% 1.59/1.80      inference('simplify', [status(thm)], ['92'])).
% 1.59/1.80  thf('94', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['91', '93'])).
% 1.59/1.80  thf('95', plain,
% 1.59/1.80      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.59/1.80        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v1_relat_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['90', '94'])).
% 1.59/1.80  thf('96', plain,
% 1.59/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 1.59/1.80      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 1.59/1.80  thf('97', plain,
% 1.59/1.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.59/1.80         ((v1_relat_1 @ X2)
% 1.59/1.80          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.59/1.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.59/1.80  thf('98', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['96', '97'])).
% 1.59/1.80  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('sup-', [status(thm)], ['33', '34'])).
% 1.59/1.80  thf('102', plain,
% 1.59/1.80      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.59/1.80      inference('demod', [status(thm)], ['95', '98', '99', '100', '101'])).
% 1.59/1.80  thf('103', plain,
% 1.59/1.80      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.59/1.80        | ~ (v1_relat_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup+', [status(thm)], ['82', '102'])).
% 1.59/1.80  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('sup-', [status(thm)], ['33', '34'])).
% 1.59/1.80  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('107', plain,
% 1.59/1.80      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 1.59/1.80  thf('108', plain,
% 1.59/1.80      (![X14 : $i, X15 : $i]:
% 1.59/1.80         (~ (v1_partfun1 @ X15 @ X14)
% 1.59/1.80          | ((k1_relat_1 @ X15) = (X14))
% 1.59/1.80          | ~ (v4_relat_1 @ X15 @ X14)
% 1.59/1.80          | ~ (v1_relat_1 @ X15))),
% 1.59/1.80      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.59/1.80  thf('109', plain,
% 1.59/1.80      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.59/1.80        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.59/1.80        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['107', '108'])).
% 1.59/1.80  thf('110', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['96', '97'])).
% 1.59/1.80  thf('111', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.59/1.80  thf('112', plain,
% 1.59/1.80      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.59/1.80  thf('113', plain,
% 1.59/1.80      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['81', '112'])).
% 1.59/1.80  thf('114', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.59/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.80  thf('115', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('116', plain,
% 1.59/1.80      (((m1_subset_1 @ sk_C @ 
% 1.59/1.80         (k1_zfmisc_1 @ 
% 1.59/1.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.59/1.80        | ~ (l1_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['114', '115'])).
% 1.59/1.80  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('118', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('demod', [status(thm)], ['116', '117'])).
% 1.59/1.80  thf('119', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.59/1.80  thf('120', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.59/1.80      inference('demod', [status(thm)], ['118', '119'])).
% 1.59/1.80  thf('121', plain,
% 1.59/1.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.59/1.80         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 1.59/1.80          | ~ (v2_funct_1 @ X25)
% 1.59/1.80          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 1.59/1.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.59/1.80          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 1.59/1.80          | ~ (v1_funct_1 @ X25))),
% 1.59/1.80      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.59/1.80  thf('122', plain,
% 1.59/1.80      ((~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.59/1.80        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.59/1.80            = (k2_funct_1 @ sk_C))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C)
% 1.59/1.80        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.59/1.80            != (k2_relat_1 @ sk_C)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['120', '121'])).
% 1.59/1.80  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('124', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.59/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.80  thf('125', plain,
% 1.59/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('126', plain,
% 1.59/1.80      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.59/1.80        | ~ (l1_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['124', '125'])).
% 1.59/1.80  thf('127', plain, ((l1_struct_0 @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('128', plain,
% 1.59/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('demod', [status(thm)], ['126', '127'])).
% 1.59/1.80  thf('129', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.59/1.80  thf('130', plain,
% 1.59/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['128', '129'])).
% 1.59/1.80  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('132', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.59/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.80  thf('133', plain,
% 1.59/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80         = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('134', plain,
% 1.59/1.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80          = (k2_struct_0 @ sk_B))
% 1.59/1.80        | ~ (l1_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['132', '133'])).
% 1.59/1.80  thf('135', plain, ((l1_struct_0 @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('136', plain,
% 1.59/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.59/1.80         = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('demod', [status(thm)], ['134', '135'])).
% 1.59/1.80  thf('137', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.59/1.80  thf('138', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.59/1.80  thf('139', plain,
% 1.59/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.59/1.80         = (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['136', '137', '138'])).
% 1.59/1.80  thf('140', plain,
% 1.59/1.80      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.59/1.80          = (k2_funct_1 @ sk_C))
% 1.59/1.80        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.59/1.80      inference('demod', [status(thm)], ['122', '123', '130', '131', '139'])).
% 1.59/1.80  thf('141', plain,
% 1.59/1.80      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.59/1.80         = (k2_funct_1 @ sk_C))),
% 1.59/1.80      inference('simplify', [status(thm)], ['140'])).
% 1.59/1.80  thf('142', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.59/1.80  thf('143', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.59/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.80  thf('144', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.59/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.80  thf('145', plain,
% 1.59/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80          != (k2_struct_0 @ sk_B)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('split', [status(esa)], ['1'])).
% 1.59/1.80  thf('146', plain,
% 1.59/1.80      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80           != (k2_struct_0 @ sk_B))
% 1.59/1.80         | ~ (l1_struct_0 @ sk_A)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['144', '145'])).
% 1.59/1.80  thf('147', plain, ((l1_struct_0 @ sk_A)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('148', plain,
% 1.59/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80          != (k2_struct_0 @ sk_B)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('demod', [status(thm)], ['146', '147'])).
% 1.59/1.80  thf('149', plain,
% 1.59/1.80      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80           != (k2_struct_0 @ sk_B))
% 1.59/1.80         | ~ (l1_struct_0 @ sk_B)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['143', '148'])).
% 1.59/1.80  thf('150', plain, ((l1_struct_0 @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('151', plain,
% 1.59/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80          != (k2_struct_0 @ sk_B)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('demod', [status(thm)], ['149', '150'])).
% 1.59/1.80  thf('152', plain,
% 1.59/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.59/1.80          != (k2_struct_0 @ sk_B)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['142', '151'])).
% 1.59/1.80  thf('153', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['15', '16'])).
% 1.59/1.80  thf('154', plain,
% 1.59/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.59/1.80          != (k2_relat_1 @ sk_C)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('demod', [status(thm)], ['152', '153'])).
% 1.59/1.80  thf('155', plain,
% 1.59/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['141', '154'])).
% 1.59/1.80  thf('156', plain,
% 1.59/1.80      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.59/1.80         <= (~
% 1.59/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80                = (k2_struct_0 @ sk_B))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['113', '155'])).
% 1.59/1.80  thf('157', plain,
% 1.59/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80          = (k2_struct_0 @ sk_B)))),
% 1.59/1.80      inference('simplify', [status(thm)], ['156'])).
% 1.59/1.80  thf('158', plain,
% 1.59/1.80      (~
% 1.59/1.80       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80          = (k2_struct_0 @ sk_A))) | 
% 1.59/1.80       ~
% 1.59/1.80       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80          = (k2_struct_0 @ sk_B)))),
% 1.59/1.80      inference('split', [status(esa)], ['1'])).
% 1.59/1.80  thf('159', plain,
% 1.59/1.80      (~
% 1.59/1.80       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.59/1.80          = (k2_struct_0 @ sk_A)))),
% 1.59/1.80      inference('sat_resolution*', [status(thm)], ['157', '158'])).
% 1.59/1.80  thf('160', plain,
% 1.59/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 1.59/1.80      inference('simpl_trail', [status(thm)], ['69', '159'])).
% 1.59/1.80  thf('161', plain,
% 1.59/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 1.59/1.80      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 1.59/1.80  thf('162', plain,
% 1.59/1.80      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.59/1.80         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.59/1.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.59/1.80  thf('163', plain,
% 1.59/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.80         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['161', '162'])).
% 1.59/1.80  thf('164', plain,
% 1.59/1.80      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['160', '163'])).
% 1.59/1.80  thf('165', plain,
% 1.59/1.80      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 1.59/1.80        | ~ (v1_relat_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['0', '164'])).
% 1.59/1.80  thf('166', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['48', '49'])).
% 1.59/1.80  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('sup-', [status(thm)], ['33', '34'])).
% 1.59/1.80  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('170', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['165', '166', '167', '168', '169'])).
% 1.59/1.80  thf('171', plain, ($false), inference('simplify', [status(thm)], ['170'])).
% 1.59/1.80  
% 1.59/1.80  % SZS output end Refutation
% 1.59/1.80  
% 1.67/1.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
