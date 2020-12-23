%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u2qhoCAin1

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:59 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  228 (3338 expanded)
%              Number of leaves         :   39 ( 990 expanded)
%              Depth                    :   26
%              Number of atoms          : 2158 (80760 expanded)
%              Number of equality atoms :  145 (4075 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('53',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','59'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('61',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X25 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','70'])).

thf('72',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','59'])).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X22 @ X24 )
       != X22 )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_tops_2 @ X23 @ X22 @ X24 )
        = ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('80',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('81',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','83'])).

thf('85',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['71','89'])).

thf('91',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('92',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('94',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','103'])).

thf('105',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('106',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('107',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('109',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['71','89'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('111',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('112',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('114',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('115',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('121',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X22 @ X24 )
       != X22 )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_tops_2 @ X23 @ X22 @ X24 )
        = ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('129',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('133',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('137',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['141','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('152',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('154',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['129','130','139','140','154'])).

thf('156',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('158',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('159',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('160',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['96'])).

thf('161',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','163'])).

thf('165',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','166'])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('169',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48','58'])).

thf('171',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','34'])).

thf('172',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('173',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('175',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('177',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','57'])).

thf('179',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['173','174','177','178'])).

thf('180',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','170','179'])).

thf('181',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','180'])).

thf('182',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','181'])).

thf('183',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['96'])).

thf('185',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['183','184'])).

thf('186',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['109','185'])).

thf('187',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['92','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u2qhoCAin1
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:33:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 331 iterations in 0.124s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.41/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.41/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.59  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.41/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.41/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.59  thf(d3_struct_0, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf(t62_tops_2, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_struct_0 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.59                 ( m1_subset_1 @
% 0.41/0.59                   C @ 
% 0.41/0.59                   ( k1_zfmisc_1 @
% 0.41/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.59               ( ( ( ( k2_relset_1 @
% 0.41/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.41/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.41/0.59                   ( v2_funct_1 @ C ) ) =>
% 0.41/0.59                 ( ( ( k1_relset_1 @
% 0.41/0.59                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.59                       ( k2_tops_2 @
% 0.41/0.59                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.41/0.59                   ( ( k2_relset_1 @
% 0.41/0.59                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.59                       ( k2_tops_2 @
% 0.41/0.59                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.59                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( l1_struct_0 @ A ) =>
% 0.41/0.59          ( ![B:$i]:
% 0.41/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.41/0.59              ( ![C:$i]:
% 0.41/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.59                    ( v1_funct_2 @
% 0.41/0.59                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.59                    ( m1_subset_1 @
% 0.41/0.59                      C @ 
% 0.41/0.59                      ( k1_zfmisc_1 @
% 0.41/0.59                        ( k2_zfmisc_1 @
% 0.41/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.59                  ( ( ( ( k2_relset_1 @
% 0.41/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.41/0.59                        ( k2_struct_0 @ B ) ) & 
% 0.41/0.59                      ( v2_funct_1 @ C ) ) =>
% 0.41/0.59                    ( ( ( k1_relset_1 @
% 0.41/0.59                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.59                          ( k2_tops_2 @
% 0.41/0.59                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.59                        ( k2_struct_0 @ B ) ) & 
% 0.41/0.59                      ( ( k2_relset_1 @
% 0.41/0.59                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.59                          ( k2_tops_2 @
% 0.41/0.59                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.59                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (((m1_subset_1 @ sk_C @ 
% 0.41/0.59         (k1_zfmisc_1 @ 
% 0.41/0.59          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.41/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (((m1_subset_1 @ sk_C @ 
% 0.41/0.59         (k1_zfmisc_1 @ 
% 0.41/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.41/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.41/0.59  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.59         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.41/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.59         = (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.59         = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.41/0.59      inference('demod', [status(thm)], ['10', '15'])).
% 0.41/0.59  thf(cc5_funct_2, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.59       ( ![C:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.41/0.59             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.41/0.59          | (v1_partfun1 @ X15 @ X16)
% 0.41/0.59          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.41/0.59          | ~ (v1_funct_1 @ X15)
% 0.41/0.59          | (v1_xboole_0 @ X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.41/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.41/0.59        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.41/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.41/0.59  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.41/0.59  thf('25', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.41/0.59        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['18', '19', '26'])).
% 0.41/0.59  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf(fc5_struct_0, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.59       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X21 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ (k2_struct_0 @ X21))
% 0.41/0.59          | ~ (l1_struct_0 @ X21)
% 0.41/0.59          | (v2_struct_0 @ X21))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.41/0.59        | (v2_struct_0 @ sk_B)
% 0.41/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('33', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('34', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('clc', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('35', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['27', '34'])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.59      inference('sup+', [status(thm)], ['5', '35'])).
% 0.41/0.59  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('38', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.41/0.59  thf(d4_partfun1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.41/0.59       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (![X18 : $i, X19 : $i]:
% 0.41/0.59         (~ (v1_partfun1 @ X19 @ X18)
% 0.41/0.59          | ((k1_relat_1 @ X19) = (X18))
% 0.41/0.59          | ~ (v4_relat_1 @ X19 @ X18)
% 0.41/0.59          | ~ (v1_relat_1 @ X19))),
% 0.41/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.59        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.41/0.59        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc2_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.41/0.59          | (v1_relat_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ 
% 0.41/0.59           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.41/0.59        | (v1_relat_1 @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.59  thf(fc6_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.59  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.41/0.59  thf(cc2_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.59         ((v4_relat_1 @ X6 @ X7)
% 0.41/0.59          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.59  thf('48', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.59  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf(t37_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.41/0.59         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (![X4 : $i]:
% 0.41/0.59         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.41/0.59          | ~ (v1_relat_1 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.41/0.59  thf('51', plain,
% 0.41/0.59      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.59  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(d9_funct_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.59       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      (![X5 : $i]:
% 0.41/0.59         (~ (v2_funct_1 @ X5)
% 0.41/0.59          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.41/0.59          | ~ (v1_funct_1 @ X5)
% 0.41/0.59          | ~ (v1_relat_1 @ X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.59        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.41/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.59  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('57', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.59      inference('demod', [status(thm)], ['51', '57'])).
% 0.41/0.59  thf('59', plain,
% 0.41/0.59      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.59  thf('60', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59          (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['4', '59'])).
% 0.41/0.59  thf(dt_k2_tops_2, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.59       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.41/0.59         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.41/0.59         ( m1_subset_1 @
% 0.41/0.59           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.41/0.59           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (k2_tops_2 @ X25 @ X26 @ X27) @ 
% 0.41/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.41/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.41/0.59          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.41/0.59          | ~ (v1_funct_1 @ X27))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.41/0.59  thf('62', plain,
% 0.41/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.59        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59             (u1_struct_0 @ sk_B))
% 0.41/0.59        | (m1_subset_1 @ 
% 0.41/0.59           (k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59            (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.59           (k1_zfmisc_1 @ 
% 0.41/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59             (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.59  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('64', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('65', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('66', plain,
% 0.41/0.59      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.59      inference('sup+', [status(thm)], ['64', '65'])).
% 0.41/0.59  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('68', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['66', '67'])).
% 0.41/0.59  thf('69', plain,
% 0.41/0.59      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.59  thf('70', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59        (u1_struct_0 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['68', '69'])).
% 0.41/0.59  thf('71', plain,
% 0.41/0.59      ((m1_subset_1 @ 
% 0.41/0.59        (k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59         (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.41/0.59      inference('demod', [status(thm)], ['62', '63', '70'])).
% 0.41/0.59  thf('72', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('73', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59          (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['4', '59'])).
% 0.41/0.59  thf(d4_tops_2, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.59       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.41/0.59         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.41/0.59  thf('74', plain,
% 0.41/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.59         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.41/0.59          | ~ (v2_funct_1 @ X24)
% 0.41/0.59          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.41/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.41/0.59          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.41/0.59          | ~ (v1_funct_1 @ X24))),
% 0.41/0.59      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.41/0.59  thf('75', plain,
% 0.41/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.59        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59             (u1_struct_0 @ sk_B))
% 0.41/0.59        | ((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59            (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C))
% 0.41/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.59        | ((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59            (u1_struct_0 @ sk_B) @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['73', '74'])).
% 0.41/0.59  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('77', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59        (u1_struct_0 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['68', '69'])).
% 0.41/0.59  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('79', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.41/0.59  thf('80', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.59         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.41/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.59  thf('81', plain,
% 0.41/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.59         = (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['79', '80'])).
% 0.41/0.59  thf('82', plain,
% 0.41/0.59      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.59  thf('83', plain,
% 0.41/0.59      (((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59         (u1_struct_0 @ sk_B) @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['81', '82'])).
% 0.41/0.59  thf('84', plain,
% 0.41/0.59      ((((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59          (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C))
% 0.41/0.59        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['75', '76', '77', '78', '83'])).
% 0.41/0.59  thf('85', plain,
% 0.41/0.59      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.41/0.59        | ~ (l1_struct_0 @ sk_B)
% 0.41/0.59        | ((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59            (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['72', '84'])).
% 0.41/0.59  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('88', plain,
% 0.41/0.59      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.41/0.59        | ((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59            (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.41/0.59      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.41/0.59  thf('89', plain,
% 0.41/0.59      (((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59         (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.41/0.59      inference('simplify', [status(thm)], ['88'])).
% 0.41/0.59  thf('90', plain,
% 0.41/0.59      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.41/0.59      inference('demod', [status(thm)], ['71', '89'])).
% 0.41/0.59  thf('91', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.59         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.41/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.59  thf('92', plain,
% 0.41/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.41/0.59         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['90', '91'])).
% 0.41/0.59  thf('93', plain,
% 0.41/0.59      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.59  thf('94', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('95', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('96', plain,
% 0.41/0.59      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59          != (k2_struct_0 @ sk_B))
% 0.41/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59            != (k2_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('97', plain,
% 0.41/0.59      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59          != (k2_struct_0 @ sk_A)))
% 0.41/0.59         <= (~
% 0.41/0.59             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59                = (k2_struct_0 @ sk_A))))),
% 0.41/0.59      inference('split', [status(esa)], ['96'])).
% 0.41/0.59  thf('98', plain,
% 0.41/0.59      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59           != (k2_struct_0 @ sk_A))
% 0.41/0.59         | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.59         <= (~
% 0.41/0.59             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59                = (k2_struct_0 @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['95', '97'])).
% 0.41/0.59  thf('99', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('100', plain,
% 0.41/0.59      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59          != (k2_struct_0 @ sk_A)))
% 0.41/0.59         <= (~
% 0.41/0.59             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59                = (k2_struct_0 @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['98', '99'])).
% 0.41/0.59  thf('101', plain,
% 0.41/0.59      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.59           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59           != (k2_struct_0 @ sk_A))
% 0.41/0.59         | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.59         <= (~
% 0.41/0.59             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59                = (k2_struct_0 @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['94', '100'])).
% 0.41/0.59  thf('102', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('103', plain,
% 0.41/0.59      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.59          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59          != (k2_struct_0 @ sk_A)))
% 0.41/0.59         <= (~
% 0.41/0.59             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59                = (k2_struct_0 @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['101', '102'])).
% 0.41/0.59  thf('104', plain,
% 0.41/0.59      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59          != (k2_struct_0 @ sk_A)))
% 0.41/0.59         <= (~
% 0.41/0.59             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59                = (k2_struct_0 @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['93', '103'])).
% 0.41/0.59  thf('105', plain,
% 0.41/0.59      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.59  thf('106', plain,
% 0.41/0.59      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.59  thf('107', plain,
% 0.41/0.59      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59          (k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59           (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59          != (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.41/0.59         <= (~
% 0.41/0.59             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59                = (k2_struct_0 @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.41/0.59  thf('108', plain,
% 0.41/0.59      (((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59         (u1_struct_0 @ sk_B) @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.41/0.59      inference('simplify', [status(thm)], ['88'])).
% 0.41/0.59  thf('109', plain,
% 0.41/0.59      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.41/0.59          != (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.41/0.59         <= (~
% 0.41/0.59             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.59                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.59                = (k2_struct_0 @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['107', '108'])).
% 0.41/0.59  thf('110', plain,
% 0.41/0.59      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.41/0.59      inference('demod', [status(thm)], ['71', '89'])).
% 0.41/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.59  thf('111', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.59         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.41/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.59  thf('112', plain,
% 0.41/0.59      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.41/0.59         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['110', '111'])).
% 0.41/0.59  thf('113', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.41/0.59  thf('114', plain,
% 0.41/0.59      (![X4 : $i]:
% 0.41/0.59         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.41/0.59          | ~ (v1_relat_1 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.41/0.59  thf('115', plain,
% 0.41/0.59      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.41/0.59        | ~ (v1_relat_1 @ sk_C))),
% 0.41/0.59      inference('sup+', [status(thm)], ['113', '114'])).
% 0.41/0.59  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.59  thf('117', plain,
% 0.41/0.59      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.59      inference('demod', [status(thm)], ['115', '116'])).
% 0.41/0.59  thf('118', plain,
% 0.41/0.59      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.59         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.41/0.59         = (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['112', '117'])).
% 0.41/0.59  thf('119', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('120', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.41/0.59  thf('121', plain,
% 0.41/0.59      (((m1_subset_1 @ sk_C @ 
% 0.41/0.59         (k1_zfmisc_1 @ 
% 0.41/0.59          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.41/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['119', '120'])).
% 0.41/0.59  thf('122', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('123', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.41/0.59      inference('demod', [status(thm)], ['121', '122'])).
% 0.41/0.59  thf('124', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('125', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.41/0.59      inference('demod', [status(thm)], ['123', '124'])).
% 0.41/0.59  thf('126', plain,
% 0.41/0.59      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.59  thf('127', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59          (k2_relat_1 @ sk_C))))),
% 0.41/0.59      inference('demod', [status(thm)], ['125', '126'])).
% 0.41/0.59  thf('128', plain,
% 0.41/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.59         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.41/0.59          | ~ (v2_funct_1 @ X24)
% 0.41/0.59          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.41/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.41/0.59          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.41/0.59          | ~ (v1_funct_1 @ X24))),
% 0.41/0.59      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.41/0.59  thf('129', plain,
% 0.41/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.59        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59             (k2_relat_1 @ sk_C))
% 0.41/0.59        | ((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59            (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))
% 0.41/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.59        | ((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59            (k2_relat_1 @ sk_C) @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['127', '128'])).
% 0.41/0.59  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('131', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('132', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['66', '67'])).
% 0.41/0.59  thf('133', plain,
% 0.41/0.59      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.41/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['131', '132'])).
% 0.41/0.59  thf('134', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('135', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['133', '134'])).
% 0.41/0.59  thf('136', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('137', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['135', '136'])).
% 0.41/0.59  thf('138', plain,
% 0.41/0.59      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.59  thf('139', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.59        (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['137', '138'])).
% 0.41/0.59  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('141', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('142', plain,
% 0.41/0.59      (![X20 : $i]:
% 0.41/0.59         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.59  thf('143', plain,
% 0.41/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.59         = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('144', plain,
% 0.41/0.59      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.59          = (k2_struct_0 @ sk_B))
% 0.41/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.59      inference('sup+', [status(thm)], ['142', '143'])).
% 0.41/0.59  thf('145', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('146', plain,
% 0.41/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.59         = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['144', '145'])).
% 0.41/0.59  thf('147', plain,
% 0.41/0.59      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.59          = (k2_struct_0 @ sk_B))
% 0.41/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['141', '146'])).
% 0.41/0.59  thf('148', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('149', plain,
% 0.41/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.59         = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['147', '148'])).
% 0.41/0.59  thf('150', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('151', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('152', plain,
% 0.41/0.60      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60         = (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.41/0.60  thf('153', plain,
% 0.41/0.60      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.60  thf('154', plain,
% 0.41/0.60      (((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.60         (k2_relat_1 @ sk_C) @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['152', '153'])).
% 0.41/0.60  thf('155', plain,
% 0.41/0.60      ((((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.60          (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))
% 0.41/0.60        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['129', '130', '139', '140', '154'])).
% 0.41/0.60  thf('156', plain,
% 0.41/0.60      (((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.60         (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['155'])).
% 0.41/0.60  thf('157', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('158', plain,
% 0.41/0.60      (![X20 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('159', plain,
% 0.41/0.60      (![X20 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('160', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('split', [status(esa)], ['96'])).
% 0.41/0.60  thf('161', plain,
% 0.41/0.60      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60           != (k2_struct_0 @ sk_B))
% 0.41/0.60         | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['159', '160'])).
% 0.41/0.60  thf('162', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('163', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['161', '162'])).
% 0.41/0.60  thf('164', plain,
% 0.41/0.60      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60           != (k2_struct_0 @ sk_B))
% 0.41/0.60         | ~ (l1_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['158', '163'])).
% 0.41/0.60  thf('165', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('166', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['164', '165'])).
% 0.41/0.60  thf('167', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['157', '166'])).
% 0.41/0.60  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('169', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.41/0.60          != (k2_relat_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['167', '168'])).
% 0.41/0.60  thf('170', plain,
% 0.41/0.60      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['40', '45', '48', '58'])).
% 0.41/0.60  thf('171', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.41/0.60      inference('clc', [status(thm)], ['27', '34'])).
% 0.41/0.60  thf('172', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         (~ (v1_partfun1 @ X19 @ X18)
% 0.41/0.60          | ((k1_relat_1 @ X19) = (X18))
% 0.41/0.60          | ~ (v4_relat_1 @ X19 @ X18)
% 0.41/0.60          | ~ (v1_relat_1 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.41/0.60  thf('173', plain,
% 0.41/0.60      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.60        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.41/0.60        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['171', '172'])).
% 0.41/0.60  thf('174', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('175', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('176', plain,
% 0.41/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.60         ((v4_relat_1 @ X6 @ X7)
% 0.41/0.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.60  thf('177', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['175', '176'])).
% 0.41/0.60  thf('178', plain,
% 0.41/0.60      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['51', '57'])).
% 0.41/0.60  thf('179', plain,
% 0.41/0.60      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['173', '174', '177', '178'])).
% 0.41/0.60  thf('180', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.60          (k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.41/0.60           (k2_relat_1 @ sk_C) @ sk_C))
% 0.41/0.60          != (k2_relat_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['169', '170', '179'])).
% 0.41/0.60  thf('181', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.41/0.60          != (k2_relat_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['156', '180'])).
% 0.41/0.60  thf('182', plain,
% 0.41/0.60      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['118', '181'])).
% 0.41/0.60  thf('183', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          = (k2_struct_0 @ sk_B)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['182'])).
% 0.41/0.60  thf('184', plain,
% 0.41/0.60      (~
% 0.41/0.60       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          = (k2_struct_0 @ sk_A))) | 
% 0.41/0.60       ~
% 0.41/0.60       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          = (k2_struct_0 @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['96'])).
% 0.41/0.60  thf('185', plain,
% 0.41/0.60      (~
% 0.41/0.60       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          = (k2_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['183', '184'])).
% 0.41/0.60  thf('186', plain,
% 0.41/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.41/0.60         != (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['109', '185'])).
% 0.41/0.60  thf('187', plain, ($false),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['92', '186'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.45/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
