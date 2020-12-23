%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nwUAPsmCts

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:52 EST 2020

% Result     : Theorem 55.38s
% Output     : Refutation 55.38s
% Verified   : 
% Statistics : Number of formulae       :  235 ( 931 expanded)
%              Number of leaves         :   38 ( 284 expanded)
%              Depth                    :   26
%              Number of atoms          : 2200 (25417 expanded)
%              Number of equality atoms :  152 (1375 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

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

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','25'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('28',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31','34'])).

thf('36',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('41',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('48',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
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

thf('50',plain,(
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

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('56',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','61'])).

thf('63',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

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

thf('70',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('75',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('91',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72','79','91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('95',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('96',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('98',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('122',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['106','107','114','122','123'])).

thf('125',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('127',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('129',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != X13 )
      | ( v1_partfun1 @ X14 @ X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('130',plain,(
    ! [X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v4_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
      | ( v1_partfun1 @ X14 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','130'])).

thf('132',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','131'])).

thf('133',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('134',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('135',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('139',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','135','136','137','138'])).

thf('140',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['97','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('146',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('148',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('149',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('152',plain,(
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

thf('153',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('158',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157'])).

thf('159',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('161',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('162',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('163',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['42'])).

thf('164',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['161','166'])).

thf('168',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','169'])).

thf('171',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('174',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('175',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('176',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','176'])).

thf('178',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','177'])).

thf('179',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['42'])).

thf('181',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['179','180'])).

thf('182',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['62','181'])).

thf('183',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('184',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('185',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['182','185'])).

thf('187',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','191'])).

thf('193',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['192'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('194',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('195',plain,(
    $false ),
    inference(demod,[status(thm)],['10','193','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nwUAPsmCts
% 0.16/0.36  % Computer   : n021.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 10:50:04 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 55.38/55.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 55.38/55.68  % Solved by: fo/fo7.sh
% 55.38/55.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 55.38/55.68  % done 686 iterations in 55.189s
% 55.38/55.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 55.38/55.68  % SZS output start Refutation
% 55.38/55.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 55.38/55.68  thf(sk_B_type, type, sk_B: $i).
% 55.38/55.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 55.38/55.68  thf(sk_C_type, type, sk_C: $i).
% 55.38/55.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 55.38/55.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 55.38/55.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 55.38/55.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 55.38/55.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 55.38/55.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 55.38/55.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 55.38/55.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 55.38/55.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 55.38/55.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 55.38/55.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 55.38/55.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 55.38/55.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 55.38/55.68  thf(sk_A_type, type, sk_A: $i).
% 55.38/55.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 55.38/55.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 55.38/55.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 55.38/55.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 55.38/55.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 55.38/55.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 55.38/55.68  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 55.38/55.68  thf(t62_tops_2, conjecture,
% 55.38/55.68    (![A:$i]:
% 55.38/55.68     ( ( l1_struct_0 @ A ) =>
% 55.38/55.68       ( ![B:$i]:
% 55.38/55.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 55.38/55.68           ( ![C:$i]:
% 55.38/55.68             ( ( ( v1_funct_1 @ C ) & 
% 55.38/55.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 55.38/55.68                 ( m1_subset_1 @
% 55.38/55.68                   C @ 
% 55.38/55.68                   ( k1_zfmisc_1 @
% 55.38/55.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 55.38/55.68               ( ( ( ( k2_relset_1 @
% 55.38/55.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 55.38/55.68                     ( k2_struct_0 @ B ) ) & 
% 55.38/55.68                   ( v2_funct_1 @ C ) ) =>
% 55.38/55.68                 ( ( ( k1_relset_1 @
% 55.38/55.68                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 55.38/55.68                       ( k2_tops_2 @
% 55.38/55.68                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 55.38/55.68                     ( k2_struct_0 @ B ) ) & 
% 55.38/55.68                   ( ( k2_relset_1 @
% 55.38/55.68                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 55.38/55.68                       ( k2_tops_2 @
% 55.38/55.68                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 55.38/55.68                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 55.38/55.68  thf(zf_stmt_0, negated_conjecture,
% 55.38/55.68    (~( ![A:$i]:
% 55.38/55.68        ( ( l1_struct_0 @ A ) =>
% 55.38/55.68          ( ![B:$i]:
% 55.38/55.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 55.38/55.68              ( ![C:$i]:
% 55.38/55.68                ( ( ( v1_funct_1 @ C ) & 
% 55.38/55.68                    ( v1_funct_2 @
% 55.38/55.68                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 55.38/55.68                    ( m1_subset_1 @
% 55.38/55.68                      C @ 
% 55.38/55.68                      ( k1_zfmisc_1 @
% 55.38/55.68                        ( k2_zfmisc_1 @
% 55.38/55.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 55.38/55.68                  ( ( ( ( k2_relset_1 @
% 55.38/55.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 55.38/55.68                        ( k2_struct_0 @ B ) ) & 
% 55.38/55.68                      ( v2_funct_1 @ C ) ) =>
% 55.38/55.68                    ( ( ( k1_relset_1 @
% 55.38/55.68                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 55.38/55.68                          ( k2_tops_2 @
% 55.38/55.68                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 55.38/55.68                        ( k2_struct_0 @ B ) ) & 
% 55.38/55.68                      ( ( k2_relset_1 @
% 55.38/55.68                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 55.38/55.68                          ( k2_tops_2 @
% 55.38/55.68                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 55.38/55.68                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 55.38/55.68    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 55.38/55.68  thf('0', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf(redefinition_k2_relset_1, axiom,
% 55.38/55.68    (![A:$i,B:$i,C:$i]:
% 55.38/55.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 55.38/55.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 55.38/55.68  thf('1', plain,
% 55.38/55.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 55.38/55.68         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 55.38/55.68          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 55.38/55.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 55.38/55.68  thf('2', plain,
% 55.38/55.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68         = (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['0', '1'])).
% 55.38/55.68  thf('3', plain,
% 55.38/55.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68         = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf(fc5_struct_0, axiom,
% 55.38/55.68    (![A:$i]:
% 55.38/55.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 55.38/55.68       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 55.38/55.68  thf('5', plain,
% 55.38/55.68      (![X22 : $i]:
% 55.38/55.68         (~ (v1_xboole_0 @ (k2_struct_0 @ X22))
% 55.38/55.68          | ~ (l1_struct_0 @ X22)
% 55.38/55.68          | (v2_struct_0 @ X22))),
% 55.38/55.68      inference('cnf', [status(esa)], [fc5_struct_0])).
% 55.38/55.68  thf('6', plain,
% 55.38/55.68      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 55.38/55.68        | (v2_struct_0 @ sk_B)
% 55.38/55.68        | ~ (l1_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup-', [status(thm)], ['4', '5'])).
% 55.38/55.68  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('8', plain,
% 55.38/55.68      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 55.38/55.68      inference('demod', [status(thm)], ['6', '7'])).
% 55.38/55.68  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('clc', [status(thm)], ['8', '9'])).
% 55.38/55.68  thf(d3_struct_0, axiom,
% 55.38/55.68    (![A:$i]:
% 55.38/55.68     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 55.38/55.68  thf('11', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('12', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('13', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('14', plain,
% 55.38/55.68      (((m1_subset_1 @ sk_C @ 
% 55.38/55.68         (k1_zfmisc_1 @ 
% 55.38/55.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_A))),
% 55.38/55.68      inference('sup+', [status(thm)], ['12', '13'])).
% 55.38/55.68  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('16', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 55.38/55.68      inference('demod', [status(thm)], ['14', '15'])).
% 55.38/55.68  thf(t132_funct_2, axiom,
% 55.38/55.68    (![A:$i,B:$i,C:$i]:
% 55.38/55.68     ( ( ( v1_funct_1 @ C ) & 
% 55.38/55.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 55.38/55.68       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 55.38/55.68           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 55.38/55.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 55.38/55.68           ( v1_partfun1 @ C @ A ) ) ) ))).
% 55.38/55.68  thf('17', plain,
% 55.38/55.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 55.38/55.68         (((X15) = (k1_xboole_0))
% 55.38/55.68          | ~ (v1_funct_1 @ X16)
% 55.38/55.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 55.38/55.68          | (v1_partfun1 @ X16 @ X17)
% 55.38/55.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 55.38/55.68          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 55.38/55.68          | ~ (v1_funct_1 @ X16))),
% 55.38/55.68      inference('cnf', [status(esa)], [t132_funct_2])).
% 55.38/55.68  thf('18', plain,
% 55.38/55.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 55.38/55.68         (~ (v1_funct_2 @ X16 @ X17 @ X15)
% 55.38/55.68          | (v1_partfun1 @ X16 @ X17)
% 55.38/55.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 55.38/55.68          | ~ (v1_funct_1 @ X16)
% 55.38/55.68          | ((X15) = (k1_xboole_0)))),
% 55.38/55.68      inference('simplify', [status(thm)], ['17'])).
% 55.38/55.68  thf('19', plain,
% 55.38/55.68      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 55.38/55.68        | ~ (v1_funct_1 @ sk_C)
% 55.38/55.68        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 55.38/55.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['16', '18'])).
% 55.38/55.68  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('21', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('22', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('23', plain,
% 55.38/55.68      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_A))),
% 55.38/55.68      inference('sup+', [status(thm)], ['21', '22'])).
% 55.38/55.68  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('25', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 55.38/55.68      inference('demod', [status(thm)], ['23', '24'])).
% 55.38/55.68  thf('26', plain,
% 55.38/55.68      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 55.38/55.68        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 55.38/55.68      inference('demod', [status(thm)], ['19', '20', '25'])).
% 55.38/55.68  thf(d4_partfun1, axiom,
% 55.38/55.68    (![A:$i,B:$i]:
% 55.38/55.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 55.38/55.68       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 55.38/55.68  thf('27', plain,
% 55.38/55.68      (![X13 : $i, X14 : $i]:
% 55.38/55.68         (~ (v1_partfun1 @ X14 @ X13)
% 55.38/55.68          | ((k1_relat_1 @ X14) = (X13))
% 55.38/55.68          | ~ (v4_relat_1 @ X14 @ X13)
% 55.38/55.68          | ~ (v1_relat_1 @ X14))),
% 55.38/55.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 55.38/55.68  thf('28', plain,
% 55.38/55.68      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 55.38/55.68        | ~ (v1_relat_1 @ sk_C)
% 55.38/55.68        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 55.38/55.68        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['26', '27'])).
% 55.38/55.68  thf('29', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf(cc1_relset_1, axiom,
% 55.38/55.68    (![A:$i,B:$i,C:$i]:
% 55.38/55.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 55.38/55.68       ( v1_relat_1 @ C ) ))).
% 55.38/55.68  thf('30', plain,
% 55.38/55.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 55.38/55.68         ((v1_relat_1 @ X1)
% 55.38/55.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 55.38/55.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 55.38/55.68  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 55.38/55.68      inference('sup-', [status(thm)], ['29', '30'])).
% 55.38/55.68  thf('32', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 55.38/55.68      inference('demod', [status(thm)], ['14', '15'])).
% 55.38/55.68  thf(cc2_relset_1, axiom,
% 55.38/55.68    (![A:$i,B:$i,C:$i]:
% 55.38/55.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 55.38/55.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 55.38/55.68  thf('33', plain,
% 55.38/55.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 55.38/55.68         ((v4_relat_1 @ X4 @ X5)
% 55.38/55.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 55.38/55.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 55.38/55.68  thf('34', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 55.38/55.68      inference('sup-', [status(thm)], ['32', '33'])).
% 55.38/55.68  thf('35', plain,
% 55.38/55.68      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 55.38/55.68        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 55.38/55.68      inference('demod', [status(thm)], ['28', '31', '34'])).
% 55.38/55.68  thf('36', plain,
% 55.38/55.68      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_B)
% 55.38/55.68        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 55.38/55.68      inference('sup+', [status(thm)], ['11', '35'])).
% 55.38/55.68  thf('37', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('39', plain,
% 55.38/55.68      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 55.38/55.68        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 55.38/55.68      inference('demod', [status(thm)], ['36', '37', '38'])).
% 55.38/55.68  thf(t55_funct_1, axiom,
% 55.38/55.68    (![A:$i]:
% 55.38/55.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 55.38/55.68       ( ( v2_funct_1 @ A ) =>
% 55.38/55.68         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 55.38/55.68           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 55.38/55.68  thf('40', plain,
% 55.38/55.68      (![X0 : $i]:
% 55.38/55.68         (~ (v2_funct_1 @ X0)
% 55.38/55.68          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 55.38/55.68          | ~ (v1_funct_1 @ X0)
% 55.38/55.68          | ~ (v1_relat_1 @ X0))),
% 55.38/55.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 55.38/55.68  thf('41', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('42', plain,
% 55.38/55.68      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          != (k2_struct_0 @ sk_B))
% 55.38/55.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68            != (k2_struct_0 @ sk_A)))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('43', plain,
% 55.38/55.68      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          != (k2_struct_0 @ sk_A)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_A))))),
% 55.38/55.68      inference('split', [status(esa)], ['42'])).
% 55.38/55.68  thf('44', plain,
% 55.38/55.68      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68           != (k2_struct_0 @ sk_A))
% 55.38/55.68         | ~ (l1_struct_0 @ sk_B)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_A))))),
% 55.38/55.68      inference('sup-', [status(thm)], ['41', '43'])).
% 55.38/55.68  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('46', plain,
% 55.38/55.68      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          != (k2_struct_0 @ sk_A)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_A))))),
% 55.38/55.68      inference('demod', [status(thm)], ['44', '45'])).
% 55.38/55.68  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('48', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('49', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf(d4_tops_2, axiom,
% 55.38/55.68    (![A:$i,B:$i,C:$i]:
% 55.38/55.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 55.38/55.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 55.38/55.68       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 55.38/55.68         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 55.38/55.68  thf('50', plain,
% 55.38/55.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 55.38/55.68         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 55.38/55.68          | ~ (v2_funct_1 @ X25)
% 55.38/55.68          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 55.38/55.68          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 55.38/55.68          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 55.38/55.68          | ~ (v1_funct_1 @ X25))),
% 55.38/55.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 55.38/55.68  thf('51', plain,
% 55.38/55.68      ((~ (v1_funct_1 @ sk_C)
% 55.38/55.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 55.38/55.68        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68            = (k2_funct_1 @ sk_C))
% 55.38/55.68        | ~ (v2_funct_1 @ sk_C)
% 55.38/55.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68            != (u1_struct_0 @ sk_B)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['49', '50'])).
% 55.38/55.68  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('53', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('54', plain, ((v2_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('55', plain,
% 55.38/55.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68         = (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['0', '1'])).
% 55.38/55.68  thf('56', plain,
% 55.38/55.68      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68          = (k2_funct_1 @ sk_C))
% 55.38/55.68        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 55.38/55.68      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 55.38/55.68  thf('57', plain,
% 55.38/55.68      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_B)
% 55.38/55.68        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68            = (k2_funct_1 @ sk_C)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['48', '56'])).
% 55.38/55.68  thf('58', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('60', plain,
% 55.38/55.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 55.38/55.68        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68            = (k2_funct_1 @ sk_C)))),
% 55.38/55.68      inference('demod', [status(thm)], ['57', '58', '59'])).
% 55.38/55.68  thf('61', plain,
% 55.38/55.68      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68         = (k2_funct_1 @ sk_C))),
% 55.38/55.68      inference('simplify', [status(thm)], ['60'])).
% 55.38/55.68  thf('62', plain,
% 55.38/55.68      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_A))))),
% 55.38/55.68      inference('demod', [status(thm)], ['46', '47', '61'])).
% 55.38/55.68  thf('63', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('64', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 55.38/55.68      inference('demod', [status(thm)], ['14', '15'])).
% 55.38/55.68  thf('65', plain,
% 55.38/55.68      (((m1_subset_1 @ sk_C @ 
% 55.38/55.68         (k1_zfmisc_1 @ 
% 55.38/55.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['63', '64'])).
% 55.38/55.68  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('67', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('demod', [status(thm)], ['65', '66'])).
% 55.38/55.68  thf('68', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('69', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 55.38/55.68      inference('demod', [status(thm)], ['67', '68'])).
% 55.38/55.68  thf(t31_funct_2, axiom,
% 55.38/55.68    (![A:$i,B:$i,C:$i]:
% 55.38/55.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 55.38/55.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 55.38/55.68       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 55.38/55.68         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 55.38/55.68           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 55.38/55.68           ( m1_subset_1 @
% 55.38/55.68             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 55.38/55.68  thf('70', plain,
% 55.38/55.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 55.38/55.68         (~ (v2_funct_1 @ X18)
% 55.38/55.68          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 55.38/55.68          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 55.38/55.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 55.38/55.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 55.38/55.68          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 55.38/55.68          | ~ (v1_funct_1 @ X18))),
% 55.38/55.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 55.38/55.68  thf('71', plain,
% 55.38/55.68      ((~ (v1_funct_1 @ sk_C)
% 55.38/55.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 55.38/55.68        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 55.38/55.68           (k1_zfmisc_1 @ 
% 55.38/55.68            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 55.38/55.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 55.38/55.68            != (k2_relat_1 @ sk_C))
% 55.38/55.68        | ~ (v2_funct_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['69', '70'])).
% 55.38/55.68  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('73', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('74', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 55.38/55.68      inference('demod', [status(thm)], ['23', '24'])).
% 55.38/55.68  thf('75', plain,
% 55.38/55.68      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['73', '74'])).
% 55.38/55.68  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('77', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('demod', [status(thm)], ['75', '76'])).
% 55.38/55.68  thf('78', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('79', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('demod', [status(thm)], ['77', '78'])).
% 55.38/55.68  thf('80', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('81', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('82', plain,
% 55.38/55.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68         = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('83', plain,
% 55.38/55.68      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68          = (k2_struct_0 @ sk_B))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_A))),
% 55.38/55.68      inference('sup+', [status(thm)], ['81', '82'])).
% 55.38/55.68  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('85', plain,
% 55.38/55.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68         = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('demod', [status(thm)], ['83', '84'])).
% 55.38/55.68  thf('86', plain,
% 55.38/55.68      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68          = (k2_struct_0 @ sk_B))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['80', '85'])).
% 55.38/55.68  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('88', plain,
% 55.38/55.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68         = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('demod', [status(thm)], ['86', '87'])).
% 55.38/55.68  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('90', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('91', plain,
% 55.38/55.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 55.38/55.68         = (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('demod', [status(thm)], ['88', '89', '90'])).
% 55.38/55.68  thf('92', plain, ((v2_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('93', plain,
% 55.38/55.68      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 55.38/55.68         (k1_zfmisc_1 @ 
% 55.38/55.68          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 55.38/55.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 55.38/55.68      inference('demod', [status(thm)], ['71', '72', '79', '91', '92'])).
% 55.38/55.68  thf('94', plain,
% 55.38/55.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 55.38/55.68      inference('simplify', [status(thm)], ['93'])).
% 55.38/55.68  thf(redefinition_k1_relset_1, axiom,
% 55.38/55.68    (![A:$i,B:$i,C:$i]:
% 55.38/55.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 55.38/55.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 55.38/55.68  thf('95', plain,
% 55.38/55.68      (![X7 : $i, X8 : $i, X9 : $i]:
% 55.38/55.68         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 55.38/55.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 55.38/55.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 55.38/55.68  thf('96', plain,
% 55.38/55.68      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 55.38/55.68         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['94', '95'])).
% 55.38/55.68  thf('97', plain,
% 55.38/55.68      (![X0 : $i]:
% 55.38/55.68         (~ (v2_funct_1 @ X0)
% 55.38/55.68          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 55.38/55.68          | ~ (v1_funct_1 @ X0)
% 55.38/55.68          | ~ (v1_relat_1 @ X0))),
% 55.38/55.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 55.38/55.68  thf('98', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('99', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('100', plain,
% 55.38/55.68      (((m1_subset_1 @ sk_C @ 
% 55.38/55.68         (k1_zfmisc_1 @ 
% 55.38/55.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['98', '99'])).
% 55.38/55.68  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('102', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('demod', [status(thm)], ['100', '101'])).
% 55.38/55.68  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('104', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 55.38/55.68      inference('demod', [status(thm)], ['102', '103'])).
% 55.38/55.68  thf('105', plain,
% 55.38/55.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 55.38/55.68         (~ (v2_funct_1 @ X18)
% 55.38/55.68          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 55.38/55.68          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 55.38/55.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 55.38/55.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 55.38/55.68          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 55.38/55.68          | ~ (v1_funct_1 @ X18))),
% 55.38/55.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 55.38/55.68  thf('106', plain,
% 55.38/55.68      ((~ (v1_funct_1 @ sk_C)
% 55.38/55.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 55.38/55.68        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 55.38/55.68           (k1_zfmisc_1 @ 
% 55.38/55.68            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 55.38/55.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 55.38/55.68            != (k2_relat_1 @ sk_C))
% 55.38/55.68        | ~ (v2_funct_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['104', '105'])).
% 55.38/55.68  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('108', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('109', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('110', plain,
% 55.38/55.68      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['108', '109'])).
% 55.38/55.68  thf('111', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('112', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('demod', [status(thm)], ['110', '111'])).
% 55.38/55.68  thf('113', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('114', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('demod', [status(thm)], ['112', '113'])).
% 55.38/55.68  thf('115', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('116', plain,
% 55.38/55.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68         = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('117', plain,
% 55.38/55.68      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68          = (k2_struct_0 @ sk_B))
% 55.38/55.68        | ~ (l1_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['115', '116'])).
% 55.38/55.68  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('119', plain,
% 55.38/55.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 55.38/55.68         = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('demod', [status(thm)], ['117', '118'])).
% 55.38/55.68  thf('120', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('121', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('122', plain,
% 55.38/55.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 55.38/55.68         = (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('demod', [status(thm)], ['119', '120', '121'])).
% 55.38/55.68  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('124', plain,
% 55.38/55.68      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 55.38/55.68         (k1_zfmisc_1 @ 
% 55.38/55.68          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 55.38/55.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 55.38/55.68      inference('demod', [status(thm)], ['106', '107', '114', '122', '123'])).
% 55.38/55.68  thf('125', plain,
% 55.38/55.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 55.38/55.68      inference('simplify', [status(thm)], ['124'])).
% 55.38/55.68  thf('126', plain,
% 55.38/55.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 55.38/55.68         ((v4_relat_1 @ X4 @ X5)
% 55.38/55.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 55.38/55.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 55.38/55.68  thf('127', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['125', '126'])).
% 55.38/55.68  thf('128', plain,
% 55.38/55.68      (![X0 : $i]:
% 55.38/55.68         (~ (v2_funct_1 @ X0)
% 55.38/55.68          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 55.38/55.68          | ~ (v1_funct_1 @ X0)
% 55.38/55.68          | ~ (v1_relat_1 @ X0))),
% 55.38/55.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 55.38/55.68  thf('129', plain,
% 55.38/55.68      (![X13 : $i, X14 : $i]:
% 55.38/55.68         (((k1_relat_1 @ X14) != (X13))
% 55.38/55.68          | (v1_partfun1 @ X14 @ X13)
% 55.38/55.68          | ~ (v4_relat_1 @ X14 @ X13)
% 55.38/55.68          | ~ (v1_relat_1 @ X14))),
% 55.38/55.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 55.38/55.68  thf('130', plain,
% 55.38/55.68      (![X14 : $i]:
% 55.38/55.68         (~ (v1_relat_1 @ X14)
% 55.38/55.68          | ~ (v4_relat_1 @ X14 @ (k1_relat_1 @ X14))
% 55.38/55.68          | (v1_partfun1 @ X14 @ (k1_relat_1 @ X14)))),
% 55.38/55.68      inference('simplify', [status(thm)], ['129'])).
% 55.38/55.68  thf('131', plain,
% 55.38/55.68      (![X0 : $i]:
% 55.38/55.68         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 55.38/55.68          | ~ (v1_relat_1 @ X0)
% 55.38/55.68          | ~ (v1_funct_1 @ X0)
% 55.38/55.68          | ~ (v2_funct_1 @ X0)
% 55.38/55.68          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 55.38/55.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['128', '130'])).
% 55.38/55.68  thf('132', plain,
% 55.38/55.68      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 55.38/55.68        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 55.38/55.68           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 55.38/55.68        | ~ (v2_funct_1 @ sk_C)
% 55.38/55.68        | ~ (v1_funct_1 @ sk_C)
% 55.38/55.68        | ~ (v1_relat_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['127', '131'])).
% 55.38/55.68  thf('133', plain,
% 55.38/55.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 55.38/55.68      inference('simplify', [status(thm)], ['124'])).
% 55.38/55.68  thf('134', plain,
% 55.38/55.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 55.38/55.68         ((v1_relat_1 @ X1)
% 55.38/55.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 55.38/55.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 55.38/55.68  thf('135', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['133', '134'])).
% 55.38/55.68  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 55.38/55.68      inference('sup-', [status(thm)], ['29', '30'])).
% 55.38/55.68  thf('139', plain,
% 55.38/55.68      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 55.38/55.68      inference('demod', [status(thm)], ['132', '135', '136', '137', '138'])).
% 55.38/55.68  thf('140', plain,
% 55.38/55.68      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 55.38/55.68        | ~ (v1_relat_1 @ sk_C)
% 55.38/55.68        | ~ (v1_funct_1 @ sk_C)
% 55.38/55.68        | ~ (v2_funct_1 @ sk_C))),
% 55.38/55.68      inference('sup+', [status(thm)], ['97', '139'])).
% 55.38/55.68  thf('141', plain, ((v1_relat_1 @ sk_C)),
% 55.38/55.68      inference('sup-', [status(thm)], ['29', '30'])).
% 55.38/55.68  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('143', plain, ((v2_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('144', plain,
% 55.38/55.68      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 55.38/55.68  thf('145', plain,
% 55.38/55.68      (![X13 : $i, X14 : $i]:
% 55.38/55.68         (~ (v1_partfun1 @ X14 @ X13)
% 55.38/55.68          | ((k1_relat_1 @ X14) = (X13))
% 55.38/55.68          | ~ (v4_relat_1 @ X14 @ X13)
% 55.38/55.68          | ~ (v1_relat_1 @ X14))),
% 55.38/55.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 55.38/55.68  thf('146', plain,
% 55.38/55.68      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 55.38/55.68        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 55.38/55.68        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['144', '145'])).
% 55.38/55.68  thf('147', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['133', '134'])).
% 55.38/55.68  thf('148', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['125', '126'])).
% 55.38/55.68  thf('149', plain,
% 55.38/55.68      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('demod', [status(thm)], ['146', '147', '148'])).
% 55.38/55.68  thf('150', plain,
% 55.38/55.68      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 55.38/55.68         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('demod', [status(thm)], ['96', '149'])).
% 55.38/55.68  thf('151', plain,
% 55.38/55.68      ((m1_subset_1 @ sk_C @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 55.38/55.68      inference('demod', [status(thm)], ['102', '103'])).
% 55.38/55.68  thf('152', plain,
% 55.38/55.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 55.38/55.68         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 55.38/55.68          | ~ (v2_funct_1 @ X25)
% 55.38/55.68          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 55.38/55.68          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 55.38/55.68          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 55.38/55.68          | ~ (v1_funct_1 @ X25))),
% 55.38/55.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 55.38/55.68  thf('153', plain,
% 55.38/55.68      ((~ (v1_funct_1 @ sk_C)
% 55.38/55.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 55.38/55.68        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 55.38/55.68            = (k2_funct_1 @ sk_C))
% 55.38/55.68        | ~ (v2_funct_1 @ sk_C)
% 55.38/55.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 55.38/55.68            != (k2_relat_1 @ sk_C)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['151', '152'])).
% 55.38/55.68  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('155', plain,
% 55.38/55.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('demod', [status(thm)], ['112', '113'])).
% 55.38/55.68  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('157', plain,
% 55.38/55.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 55.38/55.68         = (k2_relat_1 @ sk_C))),
% 55.38/55.68      inference('demod', [status(thm)], ['119', '120', '121'])).
% 55.38/55.68  thf('158', plain,
% 55.38/55.68      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 55.38/55.68          = (k2_funct_1 @ sk_C))
% 55.38/55.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 55.38/55.68      inference('demod', [status(thm)], ['153', '154', '155', '156', '157'])).
% 55.38/55.68  thf('159', plain,
% 55.38/55.68      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 55.38/55.68         = (k2_funct_1 @ sk_C))),
% 55.38/55.68      inference('simplify', [status(thm)], ['158'])).
% 55.38/55.68  thf('160', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('161', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('162', plain,
% 55.38/55.68      (![X21 : $i]:
% 55.38/55.68         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 55.38/55.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 55.38/55.68  thf('163', plain,
% 55.38/55.68      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          != (k2_struct_0 @ sk_B)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('split', [status(esa)], ['42'])).
% 55.38/55.68  thf('164', plain,
% 55.38/55.68      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68           != (k2_struct_0 @ sk_B))
% 55.38/55.68         | ~ (l1_struct_0 @ sk_B)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('sup-', [status(thm)], ['162', '163'])).
% 55.38/55.68  thf('165', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('166', plain,
% 55.38/55.68      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          != (k2_struct_0 @ sk_B)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('demod', [status(thm)], ['164', '165'])).
% 55.38/55.68  thf('167', plain,
% 55.38/55.68      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 55.38/55.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68           != (k2_struct_0 @ sk_B))
% 55.38/55.68         | ~ (l1_struct_0 @ sk_A)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('sup-', [status(thm)], ['161', '166'])).
% 55.38/55.68  thf('168', plain, ((l1_struct_0 @ sk_A)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('169', plain,
% 55.38/55.68      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          != (k2_struct_0 @ sk_B)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('demod', [status(thm)], ['167', '168'])).
% 55.38/55.68  thf('170', plain,
% 55.38/55.68      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 55.38/55.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68           != (k2_struct_0 @ sk_B))
% 55.38/55.68         | ~ (l1_struct_0 @ sk_B)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('sup-', [status(thm)], ['160', '169'])).
% 55.38/55.68  thf('171', plain, ((l1_struct_0 @ sk_B)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('172', plain,
% 55.38/55.68      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          != (k2_struct_0 @ sk_B)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('demod', [status(thm)], ['170', '171'])).
% 55.38/55.68  thf('173', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('174', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('175', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 55.38/55.68      inference('sup+', [status(thm)], ['2', '3'])).
% 55.38/55.68  thf('176', plain,
% 55.38/55.68      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 55.38/55.68          != (k2_relat_1 @ sk_C)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 55.38/55.68  thf('177', plain,
% 55.38/55.68      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('sup-', [status(thm)], ['159', '176'])).
% 55.38/55.68  thf('178', plain,
% 55.38/55.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 55.38/55.68         <= (~
% 55.38/55.68             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68                = (k2_struct_0 @ sk_B))))),
% 55.38/55.68      inference('sup-', [status(thm)], ['150', '177'])).
% 55.38/55.68  thf('179', plain,
% 55.38/55.68      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          = (k2_struct_0 @ sk_B)))),
% 55.38/55.68      inference('simplify', [status(thm)], ['178'])).
% 55.38/55.68  thf('180', plain,
% 55.38/55.68      (~
% 55.38/55.68       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          = (k2_struct_0 @ sk_A))) | 
% 55.38/55.68       ~
% 55.38/55.68       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          = (k2_struct_0 @ sk_B)))),
% 55.38/55.68      inference('split', [status(esa)], ['42'])).
% 55.38/55.68  thf('181', plain,
% 55.38/55.68      (~
% 55.38/55.68       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 55.38/55.68          = (k2_struct_0 @ sk_A)))),
% 55.38/55.68      inference('sat_resolution*', [status(thm)], ['179', '180'])).
% 55.38/55.68  thf('182', plain,
% 55.38/55.68      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 55.38/55.68      inference('simpl_trail', [status(thm)], ['62', '181'])).
% 55.38/55.68  thf('183', plain,
% 55.38/55.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 55.38/55.68        (k1_zfmisc_1 @ 
% 55.38/55.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 55.38/55.68      inference('simplify', [status(thm)], ['124'])).
% 55.38/55.68  thf('184', plain,
% 55.38/55.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 55.38/55.68         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 55.38/55.68          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 55.38/55.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 55.38/55.68  thf('185', plain,
% 55.38/55.68      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 55.38/55.68         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['183', '184'])).
% 55.38/55.68  thf('186', plain,
% 55.38/55.68      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 55.38/55.68      inference('demod', [status(thm)], ['182', '185'])).
% 55.38/55.68  thf('187', plain,
% 55.38/55.68      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 55.38/55.68        | ~ (v1_relat_1 @ sk_C)
% 55.38/55.68        | ~ (v1_funct_1 @ sk_C)
% 55.38/55.68        | ~ (v2_funct_1 @ sk_C))),
% 55.38/55.68      inference('sup-', [status(thm)], ['40', '186'])).
% 55.38/55.68  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 55.38/55.68      inference('sup-', [status(thm)], ['29', '30'])).
% 55.38/55.68  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 55.38/55.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.38/55.68  thf('191', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 55.38/55.68      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 55.38/55.68  thf('192', plain,
% 55.38/55.68      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 55.38/55.68        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 55.38/55.68      inference('sup-', [status(thm)], ['39', '191'])).
% 55.38/55.68  thf('193', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 55.38/55.68      inference('simplify', [status(thm)], ['192'])).
% 55.38/55.68  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 55.38/55.68  thf('194', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 55.38/55.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 55.38/55.68  thf('195', plain, ($false),
% 55.38/55.68      inference('demod', [status(thm)], ['10', '193', '194'])).
% 55.38/55.68  
% 55.38/55.68  % SZS output end Refutation
% 55.38/55.68  
% 55.51/55.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
