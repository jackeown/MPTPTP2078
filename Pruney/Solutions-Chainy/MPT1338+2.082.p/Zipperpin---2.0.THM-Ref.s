%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G9bkjRdgyJ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:01 EST 2020

% Result     : Theorem 51.22s
% Output     : Refutation 51.22s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 949 expanded)
%              Number of leaves         :   39 ( 290 expanded)
%              Depth                    :   26
%              Number of atoms          : 2229 (25515 expanded)
%              Number of equality atoms :  152 (1375 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X18 @ X16 )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
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
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','33','36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('43',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('50',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('58',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('61',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','63'])).

thf('65',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

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

thf('72',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('77',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('93',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74','81','93','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('97',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('98',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('100',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('124',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','116','124','125'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('129',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('131',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != X14 )
      | ( v1_partfun1 @ X15 @ X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('132',plain,(
    ! [X15: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v4_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
      | ( v1_partfun1 @ X15 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','132'])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('139',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('143',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','139','140','141','142'])).

thf('144',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['99','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('150',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('152',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('153',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('156',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('160',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('162',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','161'])).

thf('163',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('165',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('166',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('167',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('168',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['165','170'])).

thf('172',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['164','173'])).

thf('175',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('178',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('179',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('180',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','180'])).

thf('182',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','181'])).

thf('183',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('185',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['183','184'])).

thf('186',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['64','185'])).

thf('187',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('188',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('189',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['186','189'])).

thf('191',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','195'])).

thf('197',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['196'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('198',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('199',plain,(
    $false ),
    inference(demod,[status(thm)],['10','197','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G9bkjRdgyJ
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 51.22/51.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 51.22/51.46  % Solved by: fo/fo7.sh
% 51.22/51.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.22/51.46  % done 666 iterations in 50.993s
% 51.22/51.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 51.22/51.46  % SZS output start Refutation
% 51.22/51.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 51.22/51.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 51.22/51.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 51.22/51.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 51.22/51.46  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 51.22/51.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 51.22/51.46  thf(sk_C_type, type, sk_C: $i).
% 51.22/51.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 51.22/51.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 51.22/51.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 51.22/51.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.22/51.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 51.22/51.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 51.22/51.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 51.22/51.46  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 51.22/51.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 51.22/51.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 51.22/51.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 51.22/51.46  thf(sk_A_type, type, sk_A: $i).
% 51.22/51.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 51.22/51.46  thf(sk_B_type, type, sk_B: $i).
% 51.22/51.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 51.22/51.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 51.22/51.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 51.22/51.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 51.22/51.46  thf(t62_tops_2, conjecture,
% 51.22/51.46    (![A:$i]:
% 51.22/51.46     ( ( l1_struct_0 @ A ) =>
% 51.22/51.46       ( ![B:$i]:
% 51.22/51.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 51.22/51.46           ( ![C:$i]:
% 51.22/51.46             ( ( ( v1_funct_1 @ C ) & 
% 51.22/51.46                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 51.22/51.46                 ( m1_subset_1 @
% 51.22/51.46                   C @ 
% 51.22/51.46                   ( k1_zfmisc_1 @
% 51.22/51.46                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 51.22/51.46               ( ( ( ( k2_relset_1 @
% 51.22/51.46                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 51.22/51.46                     ( k2_struct_0 @ B ) ) & 
% 51.22/51.46                   ( v2_funct_1 @ C ) ) =>
% 51.22/51.46                 ( ( ( k1_relset_1 @
% 51.22/51.46                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 51.22/51.46                       ( k2_tops_2 @
% 51.22/51.46                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 51.22/51.46                     ( k2_struct_0 @ B ) ) & 
% 51.22/51.46                   ( ( k2_relset_1 @
% 51.22/51.46                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 51.22/51.46                       ( k2_tops_2 @
% 51.22/51.46                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 51.22/51.46                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 51.22/51.46  thf(zf_stmt_0, negated_conjecture,
% 51.22/51.46    (~( ![A:$i]:
% 51.22/51.46        ( ( l1_struct_0 @ A ) =>
% 51.22/51.46          ( ![B:$i]:
% 51.22/51.46            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 51.22/51.46              ( ![C:$i]:
% 51.22/51.46                ( ( ( v1_funct_1 @ C ) & 
% 51.22/51.46                    ( v1_funct_2 @
% 51.22/51.46                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 51.22/51.46                    ( m1_subset_1 @
% 51.22/51.46                      C @ 
% 51.22/51.46                      ( k1_zfmisc_1 @
% 51.22/51.46                        ( k2_zfmisc_1 @
% 51.22/51.46                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 51.22/51.46                  ( ( ( ( k2_relset_1 @
% 51.22/51.46                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 51.22/51.46                        ( k2_struct_0 @ B ) ) & 
% 51.22/51.46                      ( v2_funct_1 @ C ) ) =>
% 51.22/51.46                    ( ( ( k1_relset_1 @
% 51.22/51.46                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 51.22/51.46                          ( k2_tops_2 @
% 51.22/51.46                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 51.22/51.46                        ( k2_struct_0 @ B ) ) & 
% 51.22/51.46                      ( ( k2_relset_1 @
% 51.22/51.46                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 51.22/51.46                          ( k2_tops_2 @
% 51.22/51.46                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 51.22/51.46                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 51.22/51.46    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 51.22/51.46  thf('0', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf(redefinition_k2_relset_1, axiom,
% 51.22/51.46    (![A:$i,B:$i,C:$i]:
% 51.22/51.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 51.22/51.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 51.22/51.46  thf('1', plain,
% 51.22/51.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 51.22/51.46         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 51.22/51.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 51.22/51.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 51.22/51.46  thf('2', plain,
% 51.22/51.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46         = (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('sup-', [status(thm)], ['0', '1'])).
% 51.22/51.46  thf('3', plain,
% 51.22/51.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46         = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf(fc5_struct_0, axiom,
% 51.22/51.46    (![A:$i]:
% 51.22/51.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 51.22/51.46       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 51.22/51.46  thf('5', plain,
% 51.22/51.46      (![X23 : $i]:
% 51.22/51.46         (~ (v1_xboole_0 @ (k2_struct_0 @ X23))
% 51.22/51.46          | ~ (l1_struct_0 @ X23)
% 51.22/51.46          | (v2_struct_0 @ X23))),
% 51.22/51.46      inference('cnf', [status(esa)], [fc5_struct_0])).
% 51.22/51.46  thf('6', plain,
% 51.22/51.46      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 51.22/51.46        | (v2_struct_0 @ sk_B)
% 51.22/51.46        | ~ (l1_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup-', [status(thm)], ['4', '5'])).
% 51.22/51.46  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('8', plain,
% 51.22/51.46      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 51.22/51.46      inference('demod', [status(thm)], ['6', '7'])).
% 51.22/51.46  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('clc', [status(thm)], ['8', '9'])).
% 51.22/51.46  thf(d3_struct_0, axiom,
% 51.22/51.46    (![A:$i]:
% 51.22/51.46     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 51.22/51.46  thf('11', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('12', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('13', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('14', plain,
% 51.22/51.46      (((m1_subset_1 @ sk_C @ 
% 51.22/51.46         (k1_zfmisc_1 @ 
% 51.22/51.46          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_A))),
% 51.22/51.46      inference('sup+', [status(thm)], ['12', '13'])).
% 51.22/51.46  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('16', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 51.22/51.46      inference('demod', [status(thm)], ['14', '15'])).
% 51.22/51.46  thf(t132_funct_2, axiom,
% 51.22/51.46    (![A:$i,B:$i,C:$i]:
% 51.22/51.46     ( ( ( v1_funct_1 @ C ) & 
% 51.22/51.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 51.22/51.46       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 51.22/51.46           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 51.22/51.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 51.22/51.46           ( v1_partfun1 @ C @ A ) ) ) ))).
% 51.22/51.46  thf('17', plain,
% 51.22/51.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 51.22/51.46         (((X16) = (k1_xboole_0))
% 51.22/51.46          | ~ (v1_funct_1 @ X17)
% 51.22/51.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 51.22/51.46          | (v1_partfun1 @ X17 @ X18)
% 51.22/51.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 51.22/51.46          | ~ (v1_funct_2 @ X17 @ X18 @ X16)
% 51.22/51.46          | ~ (v1_funct_1 @ X17))),
% 51.22/51.46      inference('cnf', [status(esa)], [t132_funct_2])).
% 51.22/51.46  thf('18', plain,
% 51.22/51.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 51.22/51.46         (~ (v1_funct_2 @ X17 @ X18 @ X16)
% 51.22/51.46          | (v1_partfun1 @ X17 @ X18)
% 51.22/51.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 51.22/51.46          | ~ (v1_funct_1 @ X17)
% 51.22/51.46          | ((X16) = (k1_xboole_0)))),
% 51.22/51.46      inference('simplify', [status(thm)], ['17'])).
% 51.22/51.46  thf('19', plain,
% 51.22/51.46      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 51.22/51.46        | ~ (v1_funct_1 @ sk_C)
% 51.22/51.46        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 51.22/51.46        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['16', '18'])).
% 51.22/51.46  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('21', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('22', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('23', plain,
% 51.22/51.46      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_A))),
% 51.22/51.46      inference('sup+', [status(thm)], ['21', '22'])).
% 51.22/51.46  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('25', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 51.22/51.46      inference('demod', [status(thm)], ['23', '24'])).
% 51.22/51.46  thf('26', plain,
% 51.22/51.46      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 51.22/51.46        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 51.22/51.46      inference('demod', [status(thm)], ['19', '20', '25'])).
% 51.22/51.46  thf(d4_partfun1, axiom,
% 51.22/51.46    (![A:$i,B:$i]:
% 51.22/51.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 51.22/51.46       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 51.22/51.46  thf('27', plain,
% 51.22/51.46      (![X14 : $i, X15 : $i]:
% 51.22/51.46         (~ (v1_partfun1 @ X15 @ X14)
% 51.22/51.46          | ((k1_relat_1 @ X15) = (X14))
% 51.22/51.46          | ~ (v4_relat_1 @ X15 @ X14)
% 51.22/51.46          | ~ (v1_relat_1 @ X15))),
% 51.22/51.46      inference('cnf', [status(esa)], [d4_partfun1])).
% 51.22/51.46  thf('28', plain,
% 51.22/51.46      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 51.22/51.46        | ~ (v1_relat_1 @ sk_C)
% 51.22/51.46        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 51.22/51.46        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['26', '27'])).
% 51.22/51.46  thf('29', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf(cc2_relat_1, axiom,
% 51.22/51.46    (![A:$i]:
% 51.22/51.46     ( ( v1_relat_1 @ A ) =>
% 51.22/51.46       ( ![B:$i]:
% 51.22/51.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 51.22/51.46  thf('30', plain,
% 51.22/51.46      (![X0 : $i, X1 : $i]:
% 51.22/51.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 51.22/51.46          | (v1_relat_1 @ X0)
% 51.22/51.46          | ~ (v1_relat_1 @ X1))),
% 51.22/51.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 51.22/51.46  thf('31', plain,
% 51.22/51.46      ((~ (v1_relat_1 @ 
% 51.22/51.46           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 51.22/51.46        | (v1_relat_1 @ sk_C))),
% 51.22/51.46      inference('sup-', [status(thm)], ['29', '30'])).
% 51.22/51.46  thf(fc6_relat_1, axiom,
% 51.22/51.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 51.22/51.46  thf('32', plain,
% 51.22/51.46      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 51.22/51.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 51.22/51.46  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 51.22/51.46      inference('demod', [status(thm)], ['31', '32'])).
% 51.22/51.46  thf('34', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 51.22/51.46      inference('demod', [status(thm)], ['14', '15'])).
% 51.22/51.46  thf(cc2_relset_1, axiom,
% 51.22/51.46    (![A:$i,B:$i,C:$i]:
% 51.22/51.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 51.22/51.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 51.22/51.46  thf('35', plain,
% 51.22/51.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 51.22/51.46         ((v4_relat_1 @ X5 @ X6)
% 51.22/51.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 51.22/51.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 51.22/51.46  thf('36', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 51.22/51.46      inference('sup-', [status(thm)], ['34', '35'])).
% 51.22/51.46  thf('37', plain,
% 51.22/51.46      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 51.22/51.46        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 51.22/51.46      inference('demod', [status(thm)], ['28', '33', '36'])).
% 51.22/51.46  thf('38', plain,
% 51.22/51.46      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_B)
% 51.22/51.46        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 51.22/51.46      inference('sup+', [status(thm)], ['11', '37'])).
% 51.22/51.46  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('41', plain,
% 51.22/51.46      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 51.22/51.46        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 51.22/51.46      inference('demod', [status(thm)], ['38', '39', '40'])).
% 51.22/51.46  thf(t55_funct_1, axiom,
% 51.22/51.46    (![A:$i]:
% 51.22/51.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 51.22/51.46       ( ( v2_funct_1 @ A ) =>
% 51.22/51.46         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 51.22/51.46           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 51.22/51.46  thf('42', plain,
% 51.22/51.46      (![X4 : $i]:
% 51.22/51.46         (~ (v2_funct_1 @ X4)
% 51.22/51.46          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 51.22/51.46          | ~ (v1_funct_1 @ X4)
% 51.22/51.46          | ~ (v1_relat_1 @ X4))),
% 51.22/51.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 51.22/51.46  thf('43', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('44', plain,
% 51.22/51.46      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          != (k2_struct_0 @ sk_B))
% 51.22/51.46        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46            != (k2_struct_0 @ sk_A)))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('45', plain,
% 51.22/51.46      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          != (k2_struct_0 @ sk_A)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_A))))),
% 51.22/51.46      inference('split', [status(esa)], ['44'])).
% 51.22/51.46  thf('46', plain,
% 51.22/51.46      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46           != (k2_struct_0 @ sk_A))
% 51.22/51.46         | ~ (l1_struct_0 @ sk_B)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_A))))),
% 51.22/51.46      inference('sup-', [status(thm)], ['43', '45'])).
% 51.22/51.46  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('48', plain,
% 51.22/51.46      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          != (k2_struct_0 @ sk_A)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_A))))),
% 51.22/51.46      inference('demod', [status(thm)], ['46', '47'])).
% 51.22/51.46  thf('49', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('50', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('51', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf(d4_tops_2, axiom,
% 51.22/51.46    (![A:$i,B:$i,C:$i]:
% 51.22/51.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 51.22/51.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 51.22/51.46       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 51.22/51.46         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 51.22/51.46  thf('52', plain,
% 51.22/51.46      (![X24 : $i, X25 : $i, X26 : $i]:
% 51.22/51.46         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 51.22/51.46          | ~ (v2_funct_1 @ X26)
% 51.22/51.46          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 51.22/51.46          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 51.22/51.46          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 51.22/51.46          | ~ (v1_funct_1 @ X26))),
% 51.22/51.46      inference('cnf', [status(esa)], [d4_tops_2])).
% 51.22/51.46  thf('53', plain,
% 51.22/51.46      ((~ (v1_funct_1 @ sk_C)
% 51.22/51.46        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 51.22/51.46        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46            = (k2_funct_1 @ sk_C))
% 51.22/51.46        | ~ (v2_funct_1 @ sk_C)
% 51.22/51.46        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46            != (u1_struct_0 @ sk_B)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['51', '52'])).
% 51.22/51.46  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('55', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('57', plain,
% 51.22/51.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46         = (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('sup-', [status(thm)], ['0', '1'])).
% 51.22/51.46  thf('58', plain,
% 51.22/51.46      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46          = (k2_funct_1 @ sk_C))
% 51.22/51.46        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 51.22/51.46      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 51.22/51.46  thf('59', plain,
% 51.22/51.46      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_B)
% 51.22/51.46        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46            = (k2_funct_1 @ sk_C)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['50', '58'])).
% 51.22/51.46  thf('60', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('62', plain,
% 51.22/51.46      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 51.22/51.46        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46            = (k2_funct_1 @ sk_C)))),
% 51.22/51.46      inference('demod', [status(thm)], ['59', '60', '61'])).
% 51.22/51.46  thf('63', plain,
% 51.22/51.46      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46         = (k2_funct_1 @ sk_C))),
% 51.22/51.46      inference('simplify', [status(thm)], ['62'])).
% 51.22/51.46  thf('64', plain,
% 51.22/51.46      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_A))))),
% 51.22/51.46      inference('demod', [status(thm)], ['48', '49', '63'])).
% 51.22/51.46  thf('65', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('66', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 51.22/51.46      inference('demod', [status(thm)], ['14', '15'])).
% 51.22/51.46  thf('67', plain,
% 51.22/51.46      (((m1_subset_1 @ sk_C @ 
% 51.22/51.46         (k1_zfmisc_1 @ 
% 51.22/51.46          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['65', '66'])).
% 51.22/51.46  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('69', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('demod', [status(thm)], ['67', '68'])).
% 51.22/51.46  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('71', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 51.22/51.46      inference('demod', [status(thm)], ['69', '70'])).
% 51.22/51.46  thf(t31_funct_2, axiom,
% 51.22/51.46    (![A:$i,B:$i,C:$i]:
% 51.22/51.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 51.22/51.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 51.22/51.46       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 51.22/51.46         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 51.22/51.46           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 51.22/51.46           ( m1_subset_1 @
% 51.22/51.46             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 51.22/51.46  thf('72', plain,
% 51.22/51.46      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.22/51.46         (~ (v2_funct_1 @ X19)
% 51.22/51.46          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 51.22/51.46          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 51.22/51.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 51.22/51.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 51.22/51.46          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 51.22/51.46          | ~ (v1_funct_1 @ X19))),
% 51.22/51.46      inference('cnf', [status(esa)], [t31_funct_2])).
% 51.22/51.46  thf('73', plain,
% 51.22/51.46      ((~ (v1_funct_1 @ sk_C)
% 51.22/51.46        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 51.22/51.46        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 51.22/51.46           (k1_zfmisc_1 @ 
% 51.22/51.46            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 51.22/51.46        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 51.22/51.46            != (k2_relat_1 @ sk_C))
% 51.22/51.46        | ~ (v2_funct_1 @ sk_C))),
% 51.22/51.46      inference('sup-', [status(thm)], ['71', '72'])).
% 51.22/51.46  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('75', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('76', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 51.22/51.46      inference('demod', [status(thm)], ['23', '24'])).
% 51.22/51.46  thf('77', plain,
% 51.22/51.46      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['75', '76'])).
% 51.22/51.46  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('79', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('demod', [status(thm)], ['77', '78'])).
% 51.22/51.46  thf('80', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('81', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['79', '80'])).
% 51.22/51.46  thf('82', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('83', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('84', plain,
% 51.22/51.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46         = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('85', plain,
% 51.22/51.46      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46          = (k2_struct_0 @ sk_B))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_A))),
% 51.22/51.46      inference('sup+', [status(thm)], ['83', '84'])).
% 51.22/51.46  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('87', plain,
% 51.22/51.46      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46         = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('demod', [status(thm)], ['85', '86'])).
% 51.22/51.46  thf('88', plain,
% 51.22/51.46      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46          = (k2_struct_0 @ sk_B))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['82', '87'])).
% 51.22/51.46  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('90', plain,
% 51.22/51.46      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46         = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('demod', [status(thm)], ['88', '89'])).
% 51.22/51.46  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('93', plain,
% 51.22/51.46      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 51.22/51.46         = (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['90', '91', '92'])).
% 51.22/51.46  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('95', plain,
% 51.22/51.46      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 51.22/51.46         (k1_zfmisc_1 @ 
% 51.22/51.46          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 51.22/51.46        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 51.22/51.46      inference('demod', [status(thm)], ['73', '74', '81', '93', '94'])).
% 51.22/51.46  thf('96', plain,
% 51.22/51.46      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 51.22/51.46      inference('simplify', [status(thm)], ['95'])).
% 51.22/51.46  thf(redefinition_k1_relset_1, axiom,
% 51.22/51.46    (![A:$i,B:$i,C:$i]:
% 51.22/51.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 51.22/51.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 51.22/51.46  thf('97', plain,
% 51.22/51.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 51.22/51.46         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 51.22/51.46          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 51.22/51.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 51.22/51.46  thf('98', plain,
% 51.22/51.46      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 51.22/51.46         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['96', '97'])).
% 51.22/51.46  thf('99', plain,
% 51.22/51.46      (![X4 : $i]:
% 51.22/51.46         (~ (v2_funct_1 @ X4)
% 51.22/51.46          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 51.22/51.46          | ~ (v1_funct_1 @ X4)
% 51.22/51.46          | ~ (v1_relat_1 @ X4))),
% 51.22/51.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 51.22/51.46  thf('100', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('101', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('102', plain,
% 51.22/51.46      (((m1_subset_1 @ sk_C @ 
% 51.22/51.46         (k1_zfmisc_1 @ 
% 51.22/51.46          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['100', '101'])).
% 51.22/51.46  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('104', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('demod', [status(thm)], ['102', '103'])).
% 51.22/51.46  thf('105', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('106', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 51.22/51.46      inference('demod', [status(thm)], ['104', '105'])).
% 51.22/51.46  thf('107', plain,
% 51.22/51.46      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.22/51.46         (~ (v2_funct_1 @ X19)
% 51.22/51.46          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 51.22/51.46          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 51.22/51.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 51.22/51.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 51.22/51.46          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 51.22/51.46          | ~ (v1_funct_1 @ X19))),
% 51.22/51.46      inference('cnf', [status(esa)], [t31_funct_2])).
% 51.22/51.46  thf('108', plain,
% 51.22/51.46      ((~ (v1_funct_1 @ sk_C)
% 51.22/51.46        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 51.22/51.46        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 51.22/51.46           (k1_zfmisc_1 @ 
% 51.22/51.46            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 51.22/51.46        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 51.22/51.46            != (k2_relat_1 @ sk_C))
% 51.22/51.46        | ~ (v2_funct_1 @ sk_C))),
% 51.22/51.46      inference('sup-', [status(thm)], ['106', '107'])).
% 51.22/51.46  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('110', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('111', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('112', plain,
% 51.22/51.46      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['110', '111'])).
% 51.22/51.46  thf('113', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('114', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('demod', [status(thm)], ['112', '113'])).
% 51.22/51.46  thf('115', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('116', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['114', '115'])).
% 51.22/51.46  thf('117', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('118', plain,
% 51.22/51.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46         = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('119', plain,
% 51.22/51.46      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46          = (k2_struct_0 @ sk_B))
% 51.22/51.46        | ~ (l1_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['117', '118'])).
% 51.22/51.46  thf('120', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('121', plain,
% 51.22/51.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 51.22/51.46         = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('demod', [status(thm)], ['119', '120'])).
% 51.22/51.46  thf('122', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('123', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('124', plain,
% 51.22/51.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 51.22/51.46         = (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['121', '122', '123'])).
% 51.22/51.46  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('126', plain,
% 51.22/51.46      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 51.22/51.46         (k1_zfmisc_1 @ 
% 51.22/51.46          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 51.22/51.46        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 51.22/51.46      inference('demod', [status(thm)], ['108', '109', '116', '124', '125'])).
% 51.22/51.46  thf('127', plain,
% 51.22/51.46      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 51.22/51.46      inference('simplify', [status(thm)], ['126'])).
% 51.22/51.46  thf('128', plain,
% 51.22/51.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 51.22/51.46         ((v4_relat_1 @ X5 @ X6)
% 51.22/51.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 51.22/51.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 51.22/51.46  thf('129', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('sup-', [status(thm)], ['127', '128'])).
% 51.22/51.46  thf('130', plain,
% 51.22/51.46      (![X4 : $i]:
% 51.22/51.46         (~ (v2_funct_1 @ X4)
% 51.22/51.46          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 51.22/51.46          | ~ (v1_funct_1 @ X4)
% 51.22/51.46          | ~ (v1_relat_1 @ X4))),
% 51.22/51.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 51.22/51.46  thf('131', plain,
% 51.22/51.46      (![X14 : $i, X15 : $i]:
% 51.22/51.46         (((k1_relat_1 @ X15) != (X14))
% 51.22/51.46          | (v1_partfun1 @ X15 @ X14)
% 51.22/51.46          | ~ (v4_relat_1 @ X15 @ X14)
% 51.22/51.46          | ~ (v1_relat_1 @ X15))),
% 51.22/51.46      inference('cnf', [status(esa)], [d4_partfun1])).
% 51.22/51.46  thf('132', plain,
% 51.22/51.46      (![X15 : $i]:
% 51.22/51.46         (~ (v1_relat_1 @ X15)
% 51.22/51.46          | ~ (v4_relat_1 @ X15 @ (k1_relat_1 @ X15))
% 51.22/51.46          | (v1_partfun1 @ X15 @ (k1_relat_1 @ X15)))),
% 51.22/51.46      inference('simplify', [status(thm)], ['131'])).
% 51.22/51.46  thf('133', plain,
% 51.22/51.46      (![X0 : $i]:
% 51.22/51.46         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 51.22/51.46          | ~ (v1_relat_1 @ X0)
% 51.22/51.46          | ~ (v1_funct_1 @ X0)
% 51.22/51.46          | ~ (v2_funct_1 @ X0)
% 51.22/51.46          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 51.22/51.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['130', '132'])).
% 51.22/51.46  thf('134', plain,
% 51.22/51.46      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 51.22/51.46        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 51.22/51.46           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 51.22/51.46        | ~ (v2_funct_1 @ sk_C)
% 51.22/51.46        | ~ (v1_funct_1 @ sk_C)
% 51.22/51.46        | ~ (v1_relat_1 @ sk_C))),
% 51.22/51.46      inference('sup-', [status(thm)], ['129', '133'])).
% 51.22/51.46  thf('135', plain,
% 51.22/51.46      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 51.22/51.46      inference('simplify', [status(thm)], ['126'])).
% 51.22/51.46  thf('136', plain,
% 51.22/51.46      (![X0 : $i, X1 : $i]:
% 51.22/51.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 51.22/51.46          | (v1_relat_1 @ X0)
% 51.22/51.46          | ~ (v1_relat_1 @ X1))),
% 51.22/51.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 51.22/51.46  thf('137', plain,
% 51.22/51.46      ((~ (v1_relat_1 @ 
% 51.22/51.46           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))
% 51.22/51.46        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['135', '136'])).
% 51.22/51.46  thf('138', plain,
% 51.22/51.46      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 51.22/51.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 51.22/51.46  thf('139', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['137', '138'])).
% 51.22/51.46  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 51.22/51.46      inference('demod', [status(thm)], ['31', '32'])).
% 51.22/51.46  thf('143', plain,
% 51.22/51.46      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 51.22/51.46      inference('demod', [status(thm)], ['134', '139', '140', '141', '142'])).
% 51.22/51.46  thf('144', plain,
% 51.22/51.46      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 51.22/51.46        | ~ (v1_relat_1 @ sk_C)
% 51.22/51.46        | ~ (v1_funct_1 @ sk_C)
% 51.22/51.46        | ~ (v2_funct_1 @ sk_C))),
% 51.22/51.46      inference('sup+', [status(thm)], ['99', '143'])).
% 51.22/51.46  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 51.22/51.46      inference('demod', [status(thm)], ['31', '32'])).
% 51.22/51.46  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('148', plain,
% 51.22/51.46      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 51.22/51.46  thf('149', plain,
% 51.22/51.46      (![X14 : $i, X15 : $i]:
% 51.22/51.46         (~ (v1_partfun1 @ X15 @ X14)
% 51.22/51.46          | ((k1_relat_1 @ X15) = (X14))
% 51.22/51.46          | ~ (v4_relat_1 @ X15 @ X14)
% 51.22/51.46          | ~ (v1_relat_1 @ X15))),
% 51.22/51.46      inference('cnf', [status(esa)], [d4_partfun1])).
% 51.22/51.46  thf('150', plain,
% 51.22/51.46      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 51.22/51.46        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 51.22/51.46        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['148', '149'])).
% 51.22/51.46  thf('151', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['137', '138'])).
% 51.22/51.46  thf('152', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('sup-', [status(thm)], ['127', '128'])).
% 51.22/51.46  thf('153', plain,
% 51.22/51.46      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['150', '151', '152'])).
% 51.22/51.46  thf('154', plain,
% 51.22/51.46      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 51.22/51.46         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['98', '153'])).
% 51.22/51.46  thf('155', plain,
% 51.22/51.46      ((m1_subset_1 @ sk_C @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 51.22/51.46      inference('demod', [status(thm)], ['104', '105'])).
% 51.22/51.46  thf('156', plain,
% 51.22/51.46      (![X24 : $i, X25 : $i, X26 : $i]:
% 51.22/51.46         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 51.22/51.46          | ~ (v2_funct_1 @ X26)
% 51.22/51.46          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 51.22/51.46          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 51.22/51.46          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 51.22/51.46          | ~ (v1_funct_1 @ X26))),
% 51.22/51.46      inference('cnf', [status(esa)], [d4_tops_2])).
% 51.22/51.46  thf('157', plain,
% 51.22/51.46      ((~ (v1_funct_1 @ sk_C)
% 51.22/51.46        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 51.22/51.46        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 51.22/51.46            = (k2_funct_1 @ sk_C))
% 51.22/51.46        | ~ (v2_funct_1 @ sk_C)
% 51.22/51.46        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 51.22/51.46            != (k2_relat_1 @ sk_C)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['155', '156'])).
% 51.22/51.46  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('159', plain,
% 51.22/51.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['114', '115'])).
% 51.22/51.46  thf('160', plain, ((v2_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('161', plain,
% 51.22/51.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 51.22/51.46         = (k2_relat_1 @ sk_C))),
% 51.22/51.46      inference('demod', [status(thm)], ['121', '122', '123'])).
% 51.22/51.46  thf('162', plain,
% 51.22/51.46      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 51.22/51.46          = (k2_funct_1 @ sk_C))
% 51.22/51.46        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 51.22/51.46      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 51.22/51.46  thf('163', plain,
% 51.22/51.46      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 51.22/51.46         = (k2_funct_1 @ sk_C))),
% 51.22/51.46      inference('simplify', [status(thm)], ['162'])).
% 51.22/51.46  thf('164', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('165', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('166', plain,
% 51.22/51.46      (![X22 : $i]:
% 51.22/51.46         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 51.22/51.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.22/51.46  thf('167', plain,
% 51.22/51.46      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          != (k2_struct_0 @ sk_B)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('split', [status(esa)], ['44'])).
% 51.22/51.46  thf('168', plain,
% 51.22/51.46      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46           != (k2_struct_0 @ sk_B))
% 51.22/51.46         | ~ (l1_struct_0 @ sk_B)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('sup-', [status(thm)], ['166', '167'])).
% 51.22/51.46  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('170', plain,
% 51.22/51.46      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          != (k2_struct_0 @ sk_B)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('demod', [status(thm)], ['168', '169'])).
% 51.22/51.46  thf('171', plain,
% 51.22/51.46      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 51.22/51.46           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46           != (k2_struct_0 @ sk_B))
% 51.22/51.46         | ~ (l1_struct_0 @ sk_A)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('sup-', [status(thm)], ['165', '170'])).
% 51.22/51.46  thf('172', plain, ((l1_struct_0 @ sk_A)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('173', plain,
% 51.22/51.46      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          != (k2_struct_0 @ sk_B)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('demod', [status(thm)], ['171', '172'])).
% 51.22/51.46  thf('174', plain,
% 51.22/51.46      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 51.22/51.46           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46           != (k2_struct_0 @ sk_B))
% 51.22/51.46         | ~ (l1_struct_0 @ sk_B)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('sup-', [status(thm)], ['164', '173'])).
% 51.22/51.46  thf('175', plain, ((l1_struct_0 @ sk_B)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('176', plain,
% 51.22/51.46      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          != (k2_struct_0 @ sk_B)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('demod', [status(thm)], ['174', '175'])).
% 51.22/51.46  thf('177', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('178', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('179', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 51.22/51.46      inference('sup+', [status(thm)], ['2', '3'])).
% 51.22/51.46  thf('180', plain,
% 51.22/51.46      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 51.22/51.46          != (k2_relat_1 @ sk_C)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 51.22/51.46  thf('181', plain,
% 51.22/51.46      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('sup-', [status(thm)], ['163', '180'])).
% 51.22/51.46  thf('182', plain,
% 51.22/51.46      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 51.22/51.46         <= (~
% 51.22/51.46             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46                = (k2_struct_0 @ sk_B))))),
% 51.22/51.46      inference('sup-', [status(thm)], ['154', '181'])).
% 51.22/51.46  thf('183', plain,
% 51.22/51.46      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          = (k2_struct_0 @ sk_B)))),
% 51.22/51.46      inference('simplify', [status(thm)], ['182'])).
% 51.22/51.46  thf('184', plain,
% 51.22/51.46      (~
% 51.22/51.46       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          = (k2_struct_0 @ sk_A))) | 
% 51.22/51.46       ~
% 51.22/51.46       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          = (k2_struct_0 @ sk_B)))),
% 51.22/51.46      inference('split', [status(esa)], ['44'])).
% 51.22/51.46  thf('185', plain,
% 51.22/51.46      (~
% 51.22/51.46       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 51.22/51.46          = (k2_struct_0 @ sk_A)))),
% 51.22/51.46      inference('sat_resolution*', [status(thm)], ['183', '184'])).
% 51.22/51.46  thf('186', plain,
% 51.22/51.46      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 51.22/51.46      inference('simpl_trail', [status(thm)], ['64', '185'])).
% 51.22/51.46  thf('187', plain,
% 51.22/51.46      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 51.22/51.46        (k1_zfmisc_1 @ 
% 51.22/51.46         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 51.22/51.46      inference('simplify', [status(thm)], ['126'])).
% 51.22/51.46  thf('188', plain,
% 51.22/51.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 51.22/51.46         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 51.22/51.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 51.22/51.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 51.22/51.46  thf('189', plain,
% 51.22/51.46      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 51.22/51.46         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['187', '188'])).
% 51.22/51.46  thf('190', plain,
% 51.22/51.46      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 51.22/51.46      inference('demod', [status(thm)], ['186', '189'])).
% 51.22/51.46  thf('191', plain,
% 51.22/51.46      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 51.22/51.46        | ~ (v1_relat_1 @ sk_C)
% 51.22/51.46        | ~ (v1_funct_1 @ sk_C)
% 51.22/51.46        | ~ (v2_funct_1 @ sk_C))),
% 51.22/51.46      inference('sup-', [status(thm)], ['42', '190'])).
% 51.22/51.46  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 51.22/51.46      inference('demod', [status(thm)], ['31', '32'])).
% 51.22/51.46  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 51.22/51.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.22/51.46  thf('195', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 51.22/51.46      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 51.22/51.46  thf('196', plain,
% 51.22/51.46      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 51.22/51.46        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 51.22/51.46      inference('sup-', [status(thm)], ['41', '195'])).
% 51.22/51.46  thf('197', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 51.22/51.46      inference('simplify', [status(thm)], ['196'])).
% 51.22/51.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 51.22/51.46  thf('198', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 51.22/51.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 51.22/51.46  thf('199', plain, ($false),
% 51.22/51.46      inference('demod', [status(thm)], ['10', '197', '198'])).
% 51.22/51.46  
% 51.22/51.46  % SZS output end Refutation
% 51.22/51.46  
% 51.31/51.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
