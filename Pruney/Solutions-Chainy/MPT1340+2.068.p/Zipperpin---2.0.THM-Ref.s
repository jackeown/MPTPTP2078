%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zg2GFccxH1

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:18 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  276 (1486 expanded)
%              Number of leaves         :   44 ( 455 expanded)
%              Depth                    :   36
%              Number of atoms          : 2645 (31381 expanded)
%              Number of equality atoms :  125 ( 856 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('3',plain,(
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

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','23','26'])).

thf('28',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('49',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','54'])).

thf('56',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('57',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('63',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','61','62'])).

thf('64',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

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

thf('69',plain,(
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

thf('70',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('74',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','76','77','86'])).

thf('88',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['63','88'])).

thf('90',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

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

thf('95',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
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

thf('104',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('106',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('110',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('111',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('115',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X26 ) @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('119',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('124',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('125',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('126',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('127',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('128',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf('129',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('130',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('131',plain,(
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
    inference('sup-',[status(thm)],['129','130'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('132',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('133',plain,(
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
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
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
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
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
    inference('sup-',[status(thm)],['126','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['112'])).

thf('142',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('145',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('147',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('148',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
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
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['144','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['143','155'])).

thf('157',plain,(
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
    inference('sup-',[status(thm)],['142','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['141','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['140','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['125','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('171',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('172',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','174','175','176','177'])).

thf('179',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('180',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('185',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['112'])).

thf('186',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181','182','183','184','185'])).

thf('187',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','190'])).

thf('192',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['191','192','193','194','195'])).

thf('197',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('199',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('200',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','113','122','197','200'])).

thf('202',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['93','201'])).

thf('203',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['202','203','204','205','206'])).

thf('208',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['92','208'])).

thf('210',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('212',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['210','211','212','213'])).

thf('215',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('216',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('217',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_funct_2 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('223',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('224',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['221','222','223','224'])).

thf('226',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['215','225'])).

thf('227',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('229',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,(
    $false ),
    inference(demod,[status(thm)],['214','229'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zg2GFccxH1
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 468 iterations in 0.190s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.65  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.65  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.65  thf(t65_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X10 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X10)
% 0.45/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.45/0.65          | ~ (v1_funct_1 @ X10)
% 0.45/0.65          | ~ (v1_relat_1 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.65  thf(d3_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf(t64_tops_2, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_struct_0 @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.65                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.65                 ( m1_subset_1 @
% 0.45/0.65                   C @ 
% 0.45/0.65                   ( k1_zfmisc_1 @
% 0.45/0.65                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.65               ( ( ( ( k2_relset_1 @
% 0.45/0.65                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.65                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.65                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.65                 ( r2_funct_2 @
% 0.45/0.65                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.65                   ( k2_tops_2 @
% 0.45/0.65                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.65                     ( k2_tops_2 @
% 0.45/0.65                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.65                   C ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( l1_struct_0 @ A ) =>
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.65              ( ![C:$i]:
% 0.45/0.65                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.65                    ( v1_funct_2 @
% 0.45/0.65                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.65                    ( m1_subset_1 @
% 0.45/0.65                      C @ 
% 0.45/0.65                      ( k1_zfmisc_1 @
% 0.45/0.65                        ( k2_zfmisc_1 @
% 0.45/0.65                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.65                  ( ( ( ( k2_relset_1 @
% 0.45/0.65                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.65                        ( k2_struct_0 @ B ) ) & 
% 0.45/0.65                      ( v2_funct_1 @ C ) ) =>
% 0.45/0.65                    ( r2_funct_2 @
% 0.45/0.65                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.65                      ( k2_tops_2 @
% 0.45/0.65                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.65                        ( k2_tops_2 @
% 0.45/0.65                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.65                      C ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.65          sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.65           sk_C)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.65  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.65          sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.65           sk_C)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '7'])).
% 0.45/0.65  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.65          sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(cc5_funct_2, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.65       ( ![C:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.65             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.65          | (v1_partfun1 @ X17 @ X18)
% 0.45/0.65          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.45/0.65          | ~ (v1_funct_1 @ X17)
% 0.45/0.65          | (v1_xboole_0 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.65  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.45/0.65  thf(d4_partfun1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.65       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i]:
% 0.45/0.65         (~ (v1_partfun1 @ X21 @ X20)
% 0.45/0.65          | ((k1_relat_1 @ X21) = (X20))
% 0.45/0.65          | ~ (v4_relat_1 @ X21 @ X20)
% 0.45/0.65          | ~ (v1_relat_1 @ X21))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(cc2_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.65          | (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ 
% 0.45/0.65           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.65        | (v1_relat_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.65  thf(fc6_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.65  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(cc2_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.65         ((v4_relat_1 @ X11 @ X12)
% 0.45/0.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.65  thf('26', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['18', '23', '26'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (((m1_subset_1 @ sk_C @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.65  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.65          | (v1_partfun1 @ X17 @ X18)
% 0.45/0.65          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.45/0.65          | ~ (v1_funct_1 @ X17)
% 0.45/0.65          | (v1_xboole_0 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.65  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['36', '37'])).
% 0.45/0.65  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['34', '35', '40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i]:
% 0.45/0.65         (~ (v1_partfun1 @ X21 @ X20)
% 0.45/0.65          | ((k1_relat_1 @ X21) = (X20))
% 0.45/0.65          | ~ (v4_relat_1 @ X21 @ X20)
% 0.45/0.65          | ~ (v1_relat_1 @ X21))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.65        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.65  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.65         ((v4_relat_1 @ X11 @ X12)
% 0.45/0.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.65  thf('47', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.45/0.65  thf(fc2_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X30 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X30))
% 0.45/0.65          | ~ (l1_struct_0 @ X30)
% 0.45/0.65          | (v2_struct_0 @ X30))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.45/0.65        | (v2_struct_0 @ sk_B)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.65  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.65  thf('53', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('54', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['52', '53'])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.65        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['27', '54'])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (![X30 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X30))
% 0.45/0.65          | ~ (l1_struct_0 @ X30)
% 0.45/0.65          | (v2_struct_0 @ X30))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.45/0.65        | (v2_struct_0 @ sk_B)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.65  thf('58', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.65  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('61', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('62', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.65          sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['10', '61', '62'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (((m1_subset_1 @ sk_C @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.65      inference('sup+', [status(thm)], ['64', '65'])).
% 0.45/0.65  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.65  thf(d4_tops_2, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.65       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.65         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.65         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.45/0.65          | ~ (v2_funct_1 @ X33)
% 0.45/0.65          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.45/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.45/0.65          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.45/0.65          | ~ (v1_funct_1 @ X33))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.65  thf('70', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.65        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65            = (k2_funct_1 @ sk_C))
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65            != (k2_struct_0 @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.65  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('72', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('74', plain,
% 0.45/0.65      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.65      inference('sup+', [status(thm)], ['72', '73'])).
% 0.45/0.65  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf('80', plain,
% 0.45/0.65      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65         = (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('81', plain,
% 0.45/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65          = (k2_struct_0 @ sk_B))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['79', '80'])).
% 0.45/0.65  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('83', plain,
% 0.45/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65         = (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['81', '82'])).
% 0.45/0.65  thf('84', plain,
% 0.45/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65          = (k2_struct_0 @ sk_B))
% 0.45/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.65      inference('sup+', [status(thm)], ['78', '83'])).
% 0.45/0.65  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('86', plain,
% 0.45/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65         = (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.65  thf('87', plain,
% 0.45/0.65      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65          = (k2_funct_1 @ sk_C))
% 0.45/0.65        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['70', '71', '76', '77', '86'])).
% 0.45/0.65  thf('88', plain,
% 0.45/0.65      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65         = (k2_funct_1 @ sk_C))),
% 0.45/0.65      inference('simplify', [status(thm)], ['87'])).
% 0.45/0.65  thf('89', plain,
% 0.45/0.65      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.65          sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['63', '88'])).
% 0.45/0.65  thf('90', plain,
% 0.45/0.65      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65            (k2_funct_1 @ sk_C)) @ 
% 0.45/0.65           sk_C)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '89'])).
% 0.45/0.65  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('92', plain,
% 0.45/0.65      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.65          sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['90', '91'])).
% 0.45/0.65  thf(t55_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65       ( ( v2_funct_1 @ A ) =>
% 0.45/0.65         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.65           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('93', plain,
% 0.45/0.65      (![X8 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X8)
% 0.45/0.65          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.45/0.65          | ~ (v1_funct_1 @ X8)
% 0.45/0.65          | ~ (v1_relat_1 @ X8))),
% 0.45/0.65      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.65  thf('94', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.65  thf(t31_funct_2, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.65       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.65         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.65           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.65           ( m1_subset_1 @
% 0.45/0.65             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('95', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X26)
% 0.45/0.65          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.45/0.65          | (m1_subset_1 @ (k2_funct_1 @ X26) @ 
% 0.45/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.45/0.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.45/0.65          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.45/0.65          | ~ (v1_funct_1 @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.65  thf('96', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.65        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.65           (k1_zfmisc_1 @ 
% 0.45/0.65            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.45/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65            != (k2_struct_0 @ sk_B))
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.65  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('98', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('99', plain,
% 0.45/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65         = (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.65  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('101', plain,
% 0.45/0.65      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.45/0.65        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.45/0.65  thf('102', plain,
% 0.45/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['101'])).
% 0.45/0.65  thf('103', plain,
% 0.45/0.65      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.65         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.45/0.65          | ~ (v2_funct_1 @ X33)
% 0.45/0.65          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.45/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.45/0.65          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.45/0.65          | ~ (v1_funct_1 @ X33))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.65  thf('104', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.65             (k2_struct_0 @ sk_A))
% 0.45/0.65        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.65        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['102', '103'])).
% 0.45/0.65  thf('105', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.65  thf('106', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X26)
% 0.45/0.65          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.45/0.65          | (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.45/0.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.45/0.65          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.45/0.65          | ~ (v1_funct_1 @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.65  thf('107', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.65        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65            != (k2_struct_0 @ sk_B))
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['105', '106'])).
% 0.45/0.65  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('109', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('110', plain,
% 0.45/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65         = (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.65  thf('111', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('112', plain,
% 0.45/0.65      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 0.45/0.65  thf('113', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.65      inference('simplify', [status(thm)], ['112'])).
% 0.45/0.65  thf('114', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.65  thf('115', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X26)
% 0.45/0.65          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.45/0.65          | (v1_funct_2 @ (k2_funct_1 @ X26) @ X27 @ X28)
% 0.45/0.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.45/0.65          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.45/0.65          | ~ (v1_funct_1 @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.65  thf('116', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.65        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.65           (k2_struct_0 @ sk_A))
% 0.45/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65            != (k2_struct_0 @ sk_B))
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['114', '115'])).
% 0.45/0.65  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('118', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.65  thf('119', plain,
% 0.45/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65         = (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.65  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('121', plain,
% 0.45/0.65      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.65         (k2_struct_0 @ sk_A))
% 0.45/0.65        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 0.45/0.65  thf('122', plain,
% 0.45/0.65      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.65        (k2_struct_0 @ sk_A))),
% 0.45/0.65      inference('simplify', [status(thm)], ['121'])).
% 0.45/0.65  thf('123', plain,
% 0.45/0.65      (![X8 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X8)
% 0.45/0.65          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.45/0.65          | ~ (v1_funct_1 @ X8)
% 0.45/0.65          | ~ (v1_relat_1 @ X8))),
% 0.45/0.65      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.65  thf(dt_k2_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.65         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.65  thf('124', plain,
% 0.45/0.65      (![X4 : $i]:
% 0.45/0.65         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.65          | ~ (v1_funct_1 @ X4)
% 0.45/0.65          | ~ (v1_relat_1 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.65  thf('125', plain,
% 0.45/0.65      (![X10 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X10)
% 0.45/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.45/0.65          | ~ (v1_funct_1 @ X10)
% 0.45/0.65          | ~ (v1_relat_1 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.65  thf('126', plain,
% 0.45/0.65      (![X8 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X8)
% 0.45/0.65          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.45/0.65          | ~ (v1_funct_1 @ X8)
% 0.45/0.65          | ~ (v1_relat_1 @ X8))),
% 0.45/0.65      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.65  thf('127', plain,
% 0.45/0.65      (![X4 : $i]:
% 0.45/0.65         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.45/0.65          | ~ (v1_funct_1 @ X4)
% 0.45/0.65          | ~ (v1_relat_1 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.65  thf('128', plain,
% 0.45/0.65      (![X4 : $i]:
% 0.45/0.65         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.65          | ~ (v1_funct_1 @ X4)
% 0.45/0.65          | ~ (v1_relat_1 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.65  thf(t61_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65       ( ( v2_funct_1 @ A ) =>
% 0.45/0.65         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.45/0.65             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.45/0.65           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.45/0.65             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('129', plain,
% 0.45/0.65      (![X9 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X9)
% 0.45/0.65          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 0.45/0.65              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.45/0.65          | ~ (v1_funct_1 @ X9)
% 0.45/0.65          | ~ (v1_relat_1 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.45/0.65  thf(t48_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.65           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.45/0.65               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.45/0.65             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('130', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X5)
% 0.45/0.65          | ~ (v1_funct_1 @ X5)
% 0.45/0.65          | (v2_funct_1 @ X5)
% 0.45/0.65          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.45/0.65          | ~ (v2_funct_1 @ (k5_relat_1 @ X5 @ X6))
% 0.45/0.65          | ~ (v1_funct_1 @ X6)
% 0.45/0.65          | ~ (v1_relat_1 @ X6))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.45/0.65  thf('131', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['129', '130'])).
% 0.45/0.65  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.45/0.65  thf('132', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.45/0.65  thf('133', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['131', '132'])).
% 0.45/0.65  thf('134', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['133'])).
% 0.45/0.65  thf('135', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['128', '134'])).
% 0.45/0.65  thf('136', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['135'])).
% 0.45/0.65  thf('137', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['127', '136'])).
% 0.45/0.65  thf('138', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['137'])).
% 0.45/0.65  thf('139', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['126', '138'])).
% 0.45/0.65  thf('140', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['139'])).
% 0.45/0.65  thf('141', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.65      inference('simplify', [status(thm)], ['112'])).
% 0.45/0.65  thf('142', plain,
% 0.45/0.65      (![X4 : $i]:
% 0.45/0.65         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.65          | ~ (v1_funct_1 @ X4)
% 0.45/0.65          | ~ (v1_relat_1 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.65  thf('143', plain,
% 0.45/0.65      (![X10 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X10)
% 0.45/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.45/0.65          | ~ (v1_funct_1 @ X10)
% 0.45/0.65          | ~ (v1_relat_1 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.65  thf('144', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['139'])).
% 0.45/0.65  thf('145', plain,
% 0.45/0.65      (![X4 : $i]:
% 0.45/0.65         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.45/0.65          | ~ (v1_funct_1 @ X4)
% 0.45/0.65          | ~ (v1_relat_1 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.65  thf('146', plain,
% 0.45/0.65      (![X4 : $i]:
% 0.45/0.65         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.65          | ~ (v1_funct_1 @ X4)
% 0.45/0.65          | ~ (v1_relat_1 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.65  thf('147', plain,
% 0.45/0.65      (![X10 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X10)
% 0.45/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.45/0.65          | ~ (v1_funct_1 @ X10)
% 0.45/0.65          | ~ (v1_relat_1 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.65  thf('148', plain,
% 0.45/0.65      (![X9 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X9)
% 0.45/0.65          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 0.45/0.65              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.45/0.65          | ~ (v1_funct_1 @ X9)
% 0.45/0.65          | ~ (v1_relat_1 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.45/0.65  thf('149', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.45/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['147', '148'])).
% 0.45/0.65  thf('150', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.45/0.65              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['146', '149'])).
% 0.45/0.65  thf('151', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.45/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['150'])).
% 0.45/0.65  thf('152', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.45/0.65              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['145', '151'])).
% 0.45/0.65  thf('153', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.45/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['152'])).
% 0.45/0.65  thf('154', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.45/0.65              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['144', '153'])).
% 0.45/0.65  thf('155', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.45/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['154'])).
% 0.45/0.65  thf('156', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.45/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['143', '155'])).
% 0.45/0.65  thf('157', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.45/0.65              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['142', '156'])).
% 0.45/0.65  thf('158', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.45/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.45/0.65          | ~ (v2_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['157'])).
% 0.45/0.65  thf('159', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.65        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['141', '158'])).
% 0.45/0.65  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('162', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('163', plain,
% 0.45/0.65      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.45/0.65      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 0.45/0.65  thf('164', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.65        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['140', '163'])).
% 0.45/0.65  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('167', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('168', plain,
% 0.45/0.65      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.65         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.65      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 0.45/0.65  thf('169', plain,
% 0.45/0.65      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.65          = (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.65      inference('sup+', [status(thm)], ['125', '168'])).
% 0.45/0.65  thf('170', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.65  thf('171', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.65         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.45/0.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.65  thf('172', plain,
% 0.45/0.65      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65         = (k2_relat_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['170', '171'])).
% 0.45/0.65  thf('173', plain,
% 0.45/0.65      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.65         = (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('174', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.65      inference('sup+', [status(thm)], ['172', '173'])).
% 0.45/0.65  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('177', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('178', plain,
% 0.45/0.65      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.65         = (k6_relat_1 @ (k2_struct_0 @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['169', '174', '175', '176', '177'])).
% 0.45/0.65  thf('179', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X5)
% 0.45/0.65          | ~ (v1_funct_1 @ X5)
% 0.45/0.65          | (v2_funct_1 @ X5)
% 0.45/0.65          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.45/0.65          | ~ (v2_funct_1 @ (k5_relat_1 @ X5 @ X6))
% 0.45/0.65          | ~ (v1_funct_1 @ X6)
% 0.45/0.65          | ~ (v1_relat_1 @ X6))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.45/0.65  thf('180', plain,
% 0.45/0.65      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_struct_0 @ sk_B)))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.65        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['178', '179'])).
% 0.45/0.65  thf('181', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.45/0.65  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('184', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['52', '53'])).
% 0.45/0.65  thf('185', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.65      inference('simplify', [status(thm)], ['112'])).
% 0.45/0.65  thf('186', plain,
% 0.45/0.65      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.45/0.65        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.65      inference('demod', [status(thm)],
% 0.45/0.65                ['180', '181', '182', '183', '184', '185'])).
% 0.45/0.65  thf('187', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['124', '186'])).
% 0.45/0.65  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('190', plain,
% 0.45/0.65      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['187', '188', '189'])).
% 0.45/0.65  thf('191', plain,
% 0.45/0.65      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.65        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['123', '190'])).
% 0.45/0.65  thf('192', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['52', '53'])).
% 0.45/0.65  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('195', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('196', plain,
% 0.45/0.65      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.45/0.65        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.65      inference('demod', [status(thm)], ['191', '192', '193', '194', '195'])).
% 0.45/0.65  thf('197', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.65      inference('simplify', [status(thm)], ['196'])).
% 0.45/0.65  thf('198', plain,
% 0.45/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.65      inference('simplify', [status(thm)], ['101'])).
% 0.45/0.65  thf('199', plain,
% 0.45/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.65         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.45/0.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.65  thf('200', plain,
% 0.45/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['198', '199'])).
% 0.45/0.65  thf('201', plain,
% 0.45/0.65      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.65        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['104', '113', '122', '197', '200'])).
% 0.45/0.65  thf('202', plain,
% 0.45/0.65      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.65        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['93', '201'])).
% 0.45/0.65  thf('203', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['52', '53'])).
% 0.45/0.65  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('206', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('207', plain,
% 0.45/0.65      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.45/0.65        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.65      inference('demod', [status(thm)], ['202', '203', '204', '205', '206'])).
% 0.45/0.65  thf('208', plain,
% 0.45/0.65      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.65         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['207'])).
% 0.45/0.65  thf('209', plain,
% 0.45/0.65      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.65          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['92', '208'])).
% 0.45/0.65  thf('210', plain,
% 0.45/0.65      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.65           sk_C)
% 0.45/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['0', '209'])).
% 0.45/0.65  thf('211', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('212', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('213', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('214', plain,
% 0.45/0.65      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.65          sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['210', '211', '212', '213'])).
% 0.45/0.65  thf('215', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.65  thf('216', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ 
% 0.45/0.65        (k1_zfmisc_1 @ 
% 0.45/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(reflexivity_r2_funct_2, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.65         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.65       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.45/0.65  thf('217', plain,
% 0.45/0.65      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.65         ((r2_funct_2 @ X22 @ X23 @ X24 @ X24)
% 0.45/0.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.65          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.45/0.65          | ~ (v1_funct_1 @ X24)
% 0.45/0.65          | ~ (v1_funct_1 @ X25)
% 0.45/0.65          | ~ (v1_funct_2 @ X25 @ X22 @ X23)
% 0.45/0.65          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.45/0.65      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.45/0.65  thf('218', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.65          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.65          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.65             sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['216', '217'])).
% 0.45/0.65  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('220', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('221', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.65          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.65             sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['218', '219', '220'])).
% 0.45/0.65  thf('222', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('223', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('224', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('clc', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('225', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.65          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.65             sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['221', '222', '223', '224'])).
% 0.45/0.65  thf('226', plain,
% 0.45/0.65      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['215', '225'])).
% 0.45/0.65  thf('227', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('228', plain,
% 0.45/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('229', plain,
% 0.45/0.65      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.65      inference('demod', [status(thm)], ['226', '227', '228'])).
% 0.45/0.65  thf('230', plain, ($false), inference('demod', [status(thm)], ['214', '229'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
