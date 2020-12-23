%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lMzv9rxJ5Q

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:23 EST 2020

% Result     : Theorem 5.07s
% Output     : Refutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :  323 (5035 expanded)
%              Number of leaves         :   45 (1474 expanded)
%              Depth                    :   37
%              Number of atoms          : 3045 (109851 expanded)
%              Number of equality atoms :  165 (3763 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('35',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('46',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_tops_2 @ X31 @ X30 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('76',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('82',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57','66','67','85'])).

thf('87',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','41','42','43','44','45','87'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('89',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

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

thf('91',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('95',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_tops_2 @ X31 @ X30 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('102',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('107',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('111',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('120',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('121',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','109','118','121'])).

thf('123',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('124',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('125',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('126',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('127',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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

thf('128',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
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
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
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
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('137',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('138',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('143',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('147',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('149',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('150',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144','147','150','151'])).

thf('153',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['138','152'])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('155',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('159',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('161',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('162',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('163',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('164',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('167',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','169'])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('172',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['159','160','174'])).

thf('176',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('177',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('178',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['175','178'])).

thf('180',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['137','179'])).

thf('181',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('184',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['180','185','186','187'])).

thf('189',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['136','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['183','184'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('196',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('198',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('199',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('200',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('201',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('202',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('204',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['173'])).

thf('205',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('207',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['199','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['183','184'])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['208','209','210','211'])).

thf('213',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['198','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['183','184'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['213','214','215','216'])).

thf('218',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('220',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['197','220'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('223',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('224',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('225',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('227',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('230',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('231',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['222','231'])).

thf('233',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('234',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['183','184'])).

thf('236',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['221','234','235','236','237'])).

thf('239',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['196','238'])).

thf('240',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['135','239'])).

thf('241',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('243',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('245',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('247',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['240','245','246'])).

thf('248',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['123','247'])).

thf('249',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['183','184'])).

thf('250',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['248','249','250','251'])).

thf('253',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','252'])).

thf('254',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['89','254'])).

thf('256',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['183','184'])).

thf('257',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['255','256','257','258'])).

thf('260',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['88','259'])).

thf('261',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','260'])).

thf('262',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('263',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('264',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_funct_2 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('265',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['262','268'])).

thf('270',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('272',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['269','270','271'])).

thf('273',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['183','184'])).

thf('274',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    $false ),
    inference(demod,[status(thm)],['261','272','273','274','275'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lMzv9rxJ5Q
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:03:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.07/5.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.07/5.25  % Solved by: fo/fo7.sh
% 5.07/5.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.07/5.25  % done 1201 iterations in 4.785s
% 5.07/5.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.07/5.25  % SZS output start Refutation
% 5.07/5.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.07/5.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.07/5.25  thf(sk_A_type, type, sk_A: $i).
% 5.07/5.25  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.07/5.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.07/5.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.07/5.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.07/5.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.07/5.25  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.07/5.25  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.07/5.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.07/5.25  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.07/5.25  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.07/5.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.07/5.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.07/5.25  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.07/5.25  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.07/5.25  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.07/5.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.07/5.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.07/5.25  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 5.07/5.25  thf(sk_B_type, type, sk_B: $i).
% 5.07/5.25  thf(sk_C_type, type, sk_C: $i).
% 5.07/5.25  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 5.07/5.25  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.07/5.25  thf(t65_funct_1, axiom,
% 5.07/5.25    (![A:$i]:
% 5.07/5.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.07/5.25       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 5.07/5.25  thf('0', plain,
% 5.07/5.25      (![X6 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X6)
% 5.07/5.25          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 5.07/5.25          | ~ (v1_funct_1 @ X6)
% 5.07/5.25          | ~ (v1_relat_1 @ X6))),
% 5.07/5.25      inference('cnf', [status(esa)], [t65_funct_1])).
% 5.07/5.25  thf(d3_struct_0, axiom,
% 5.07/5.25    (![A:$i]:
% 5.07/5.25     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.07/5.25  thf('1', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf('2', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf(t64_tops_2, conjecture,
% 5.07/5.25    (![A:$i]:
% 5.07/5.25     ( ( l1_struct_0 @ A ) =>
% 5.07/5.25       ( ![B:$i]:
% 5.07/5.25         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 5.07/5.25           ( ![C:$i]:
% 5.07/5.25             ( ( ( v1_funct_1 @ C ) & 
% 5.07/5.25                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.07/5.25                 ( m1_subset_1 @
% 5.07/5.25                   C @ 
% 5.07/5.25                   ( k1_zfmisc_1 @
% 5.07/5.25                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.07/5.25               ( ( ( ( k2_relset_1 @
% 5.07/5.25                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 5.07/5.25                     ( k2_struct_0 @ B ) ) & 
% 5.07/5.25                   ( v2_funct_1 @ C ) ) =>
% 5.07/5.25                 ( r2_funct_2 @
% 5.07/5.25                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 5.07/5.25                   ( k2_tops_2 @
% 5.07/5.25                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.07/5.25                     ( k2_tops_2 @
% 5.07/5.25                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 5.07/5.25                   C ) ) ) ) ) ) ))).
% 5.07/5.25  thf(zf_stmt_0, negated_conjecture,
% 5.07/5.25    (~( ![A:$i]:
% 5.07/5.25        ( ( l1_struct_0 @ A ) =>
% 5.07/5.25          ( ![B:$i]:
% 5.07/5.25            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 5.07/5.25              ( ![C:$i]:
% 5.07/5.25                ( ( ( v1_funct_1 @ C ) & 
% 5.07/5.25                    ( v1_funct_2 @
% 5.07/5.25                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.07/5.25                    ( m1_subset_1 @
% 5.07/5.25                      C @ 
% 5.07/5.25                      ( k1_zfmisc_1 @
% 5.07/5.25                        ( k2_zfmisc_1 @
% 5.07/5.25                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.07/5.25                  ( ( ( ( k2_relset_1 @
% 5.07/5.25                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 5.07/5.25                        ( k2_struct_0 @ B ) ) & 
% 5.07/5.25                      ( v2_funct_1 @ C ) ) =>
% 5.07/5.25                    ( r2_funct_2 @
% 5.07/5.25                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 5.07/5.25                      ( k2_tops_2 @
% 5.07/5.25                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.07/5.25                        ( k2_tops_2 @
% 5.07/5.25                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 5.07/5.25                      C ) ) ) ) ) ) ) )),
% 5.07/5.25    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 5.07/5.25  thf('3', plain,
% 5.07/5.25      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.07/5.25           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 5.07/5.25          sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('4', plain,
% 5.07/5.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.07/5.25            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 5.07/5.25           sk_C)
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup-', [status(thm)], ['2', '3'])).
% 5.07/5.25  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('6', plain,
% 5.07/5.25      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.07/5.25           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 5.07/5.25          sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['4', '5'])).
% 5.07/5.25  thf('7', plain,
% 5.07/5.25      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.07/5.25            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 5.07/5.25           sk_C)
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup-', [status(thm)], ['1', '6'])).
% 5.07/5.25  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('9', plain,
% 5.07/5.25      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.07/5.25           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 5.07/5.25          sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['7', '8'])).
% 5.07/5.25  thf('10', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf(d1_funct_2, axiom,
% 5.07/5.25    (![A:$i,B:$i,C:$i]:
% 5.07/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.07/5.25       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.07/5.25           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.07/5.25             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.07/5.25         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.07/5.25           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.07/5.25             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.07/5.25  thf(zf_stmt_1, axiom,
% 5.07/5.25    (![B:$i,A:$i]:
% 5.07/5.25     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.07/5.25       ( zip_tseitin_0 @ B @ A ) ))).
% 5.07/5.25  thf('11', plain,
% 5.07/5.25      (![X13 : $i, X14 : $i]:
% 5.07/5.25         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.07/5.25  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.07/5.25  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.07/5.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.07/5.25  thf('13', plain,
% 5.07/5.25      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.07/5.25      inference('sup+', [status(thm)], ['11', '12'])).
% 5.07/5.25  thf('14', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.07/5.25  thf(zf_stmt_3, axiom,
% 5.07/5.25    (![C:$i,B:$i,A:$i]:
% 5.07/5.25     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.07/5.25       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.07/5.25  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.07/5.25  thf(zf_stmt_5, axiom,
% 5.07/5.25    (![A:$i,B:$i,C:$i]:
% 5.07/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.07/5.25       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.07/5.25         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.07/5.25           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.07/5.25             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.07/5.25  thf('15', plain,
% 5.07/5.25      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.07/5.25         (~ (zip_tseitin_0 @ X18 @ X19)
% 5.07/5.25          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 5.07/5.25          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.07/5.25  thf('16', plain,
% 5.07/5.25      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.07/5.25        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['14', '15'])).
% 5.07/5.25  thf('17', plain,
% 5.07/5.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 5.07/5.25        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['13', '16'])).
% 5.07/5.25  thf('18', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('19', plain,
% 5.07/5.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.07/5.25         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 5.07/5.25          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 5.07/5.25          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.07/5.25  thf('20', plain,
% 5.07/5.25      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.07/5.25        | ((u1_struct_0 @ sk_A)
% 5.07/5.25            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['18', '19'])).
% 5.07/5.25  thf('21', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf(redefinition_k1_relset_1, axiom,
% 5.07/5.25    (![A:$i,B:$i,C:$i]:
% 5.07/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.07/5.25       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.07/5.25  thf('22', plain,
% 5.07/5.25      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.07/5.25         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 5.07/5.25          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 5.07/5.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.07/5.25  thf('23', plain,
% 5.07/5.25      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25         = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['21', '22'])).
% 5.07/5.25  thf('24', plain,
% 5.07/5.25      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.07/5.25        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['20', '23'])).
% 5.07/5.25  thf('25', plain,
% 5.07/5.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 5.07/5.25        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['17', '24'])).
% 5.07/5.25  thf('26', plain,
% 5.07/5.25      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B)
% 5.07/5.25        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('sup+', [status(thm)], ['10', '25'])).
% 5.07/5.25  thf('27', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf(redefinition_k2_relset_1, axiom,
% 5.07/5.25    (![A:$i,B:$i,C:$i]:
% 5.07/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.07/5.25       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.07/5.25  thf('28', plain,
% 5.07/5.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.07/5.25         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 5.07/5.25          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 5.07/5.25      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.07/5.25  thf('29', plain,
% 5.07/5.25      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['27', '28'])).
% 5.07/5.25  thf('30', plain,
% 5.07/5.25      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25         = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('33', plain,
% 5.07/5.25      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 5.07/5.25        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['26', '31', '32'])).
% 5.07/5.25  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf(fc5_struct_0, axiom,
% 5.07/5.25    (![A:$i]:
% 5.07/5.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 5.07/5.25       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 5.07/5.25  thf('35', plain,
% 5.07/5.25      (![X29 : $i]:
% 5.07/5.25         (~ (v1_xboole_0 @ (k2_struct_0 @ X29))
% 5.07/5.25          | ~ (l1_struct_0 @ X29)
% 5.07/5.25          | (v2_struct_0 @ X29))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc5_struct_0])).
% 5.07/5.25  thf('36', plain,
% 5.07/5.25      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 5.07/5.25        | (v2_struct_0 @ sk_B)
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup-', [status(thm)], ['34', '35'])).
% 5.07/5.25  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('38', plain,
% 5.07/5.25      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 5.07/5.25      inference('demod', [status(thm)], ['36', '37'])).
% 5.07/5.25  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('40', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['38', '39'])).
% 5.07/5.25  thf('41', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('42', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('43', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('44', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('45', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('46', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf('47', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('48', plain,
% 5.07/5.25      (((m1_subset_1 @ sk_C @ 
% 5.07/5.25         (k1_zfmisc_1 @ 
% 5.07/5.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['46', '47'])).
% 5.07/5.25  thf('49', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('50', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 5.07/5.25      inference('demod', [status(thm)], ['48', '49'])).
% 5.07/5.25  thf('51', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('52', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 5.07/5.25      inference('demod', [status(thm)], ['50', '51'])).
% 5.07/5.25  thf('53', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('54', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.07/5.25      inference('demod', [status(thm)], ['52', '53'])).
% 5.07/5.25  thf(d4_tops_2, axiom,
% 5.07/5.25    (![A:$i,B:$i,C:$i]:
% 5.07/5.25     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.07/5.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.07/5.25       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 5.07/5.25         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 5.07/5.25  thf('55', plain,
% 5.07/5.25      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.07/5.25         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 5.07/5.25          | ~ (v2_funct_1 @ X32)
% 5.07/5.25          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 5.07/5.25          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 5.07/5.25          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 5.07/5.25          | ~ (v1_funct_1 @ X32))),
% 5.07/5.25      inference('cnf', [status(esa)], [d4_tops_2])).
% 5.07/5.25  thf('56', plain,
% 5.07/5.25      ((~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.07/5.25        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25            = (k2_funct_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C)
% 5.07/5.25        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25            != (k2_relat_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['54', '55'])).
% 5.07/5.25  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('58', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf('59', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('60', plain,
% 5.07/5.25      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['58', '59'])).
% 5.07/5.25  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('62', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('demod', [status(thm)], ['60', '61'])).
% 5.07/5.25  thf('63', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('64', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['62', '63'])).
% 5.07/5.25  thf('65', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('66', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['64', '65'])).
% 5.07/5.25  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('68', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf('69', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf('70', plain,
% 5.07/5.25      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25         = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('71', plain,
% 5.07/5.25      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25          = (k2_struct_0 @ sk_B))
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['69', '70'])).
% 5.07/5.25  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('73', plain,
% 5.07/5.25      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25         = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('demod', [status(thm)], ['71', '72'])).
% 5.07/5.25  thf('74', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('75', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('76', plain,
% 5.07/5.25      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['73', '74', '75'])).
% 5.07/5.25  thf('77', plain,
% 5.07/5.25      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25          = (k2_relat_1 @ sk_C))
% 5.07/5.25        | ~ (l1_struct_0 @ sk_A))),
% 5.07/5.25      inference('sup+', [status(thm)], ['68', '76'])).
% 5.07/5.25  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('79', plain,
% 5.07/5.25      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['77', '78'])).
% 5.07/5.25  thf('80', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf('81', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('82', plain,
% 5.07/5.25      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 5.07/5.25      inference('sup+', [status(thm)], ['80', '81'])).
% 5.07/5.25  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('84', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['82', '83'])).
% 5.07/5.25  thf('85', plain,
% 5.07/5.25      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['79', '84'])).
% 5.07/5.25  thf('86', plain,
% 5.07/5.25      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25          = (k2_funct_1 @ sk_C))
% 5.07/5.25        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['56', '57', '66', '67', '85'])).
% 5.07/5.25  thf('87', plain,
% 5.07/5.25      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25         = (k2_funct_1 @ sk_C))),
% 5.07/5.25      inference('simplify', [status(thm)], ['86'])).
% 5.07/5.25  thf('88', plain,
% 5.07/5.25      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25           (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25          sk_C)),
% 5.07/5.25      inference('demod', [status(thm)],
% 5.07/5.25                ['9', '41', '42', '43', '44', '45', '87'])).
% 5.07/5.25  thf(fc6_funct_1, axiom,
% 5.07/5.25    (![A:$i]:
% 5.07/5.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 5.07/5.25       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.07/5.25         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 5.07/5.25         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.07/5.25  thf('89', plain,
% 5.07/5.25      (![X4 : $i]:
% 5.07/5.25         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 5.07/5.25          | ~ (v2_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_relat_1 @ X4))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.07/5.25  thf('90', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.07/5.25      inference('demod', [status(thm)], ['52', '53'])).
% 5.07/5.25  thf(t31_funct_2, axiom,
% 5.07/5.25    (![A:$i,B:$i,C:$i]:
% 5.07/5.25     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.07/5.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.07/5.25       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.07/5.25         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.07/5.25           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.07/5.25           ( m1_subset_1 @
% 5.07/5.25             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 5.07/5.25  thf('91', plain,
% 5.07/5.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X25)
% 5.07/5.25          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 5.07/5.25          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 5.07/5.25             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 5.07/5.25          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 5.07/5.25          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 5.07/5.25          | ~ (v1_funct_1 @ X25))),
% 5.07/5.25      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.07/5.25  thf('92', plain,
% 5.07/5.25      ((~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.07/5.25        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25           (k1_zfmisc_1 @ 
% 5.07/5.25            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 5.07/5.25        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25            != (k2_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['90', '91'])).
% 5.07/5.25  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('94', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['64', '65'])).
% 5.07/5.25  thf('95', plain,
% 5.07/5.25      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['79', '84'])).
% 5.07/5.25  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('97', plain,
% 5.07/5.25      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25         (k1_zfmisc_1 @ 
% 5.07/5.25          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 5.07/5.25        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 5.07/5.25  thf('98', plain,
% 5.07/5.25      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 5.07/5.25      inference('simplify', [status(thm)], ['97'])).
% 5.07/5.25  thf('99', plain,
% 5.07/5.25      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.07/5.25         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 5.07/5.25          | ~ (v2_funct_1 @ X32)
% 5.07/5.25          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 5.07/5.25          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 5.07/5.25          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 5.07/5.25          | ~ (v1_funct_1 @ X32))),
% 5.07/5.25      inference('cnf', [status(esa)], [d4_tops_2])).
% 5.07/5.25  thf('100', plain,
% 5.07/5.25      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 5.07/5.25             (k1_relat_1 @ sk_C))
% 5.07/5.25        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['98', '99'])).
% 5.07/5.25  thf('101', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.07/5.25      inference('demod', [status(thm)], ['52', '53'])).
% 5.07/5.25  thf('102', plain,
% 5.07/5.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X25)
% 5.07/5.25          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 5.07/5.25          | (v1_funct_1 @ (k2_funct_1 @ X25))
% 5.07/5.25          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 5.07/5.25          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 5.07/5.25          | ~ (v1_funct_1 @ X25))),
% 5.07/5.25      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.07/5.25  thf('103', plain,
% 5.07/5.25      ((~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.07/5.25        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25            != (k2_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['101', '102'])).
% 5.07/5.25  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('105', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['64', '65'])).
% 5.07/5.25  thf('106', plain,
% 5.07/5.25      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['79', '84'])).
% 5.07/5.25  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('108', plain,
% 5.07/5.25      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 5.07/5.25  thf('109', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.07/5.25      inference('simplify', [status(thm)], ['108'])).
% 5.07/5.25  thf('110', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.07/5.25      inference('demod', [status(thm)], ['52', '53'])).
% 5.07/5.25  thf('111', plain,
% 5.07/5.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X25)
% 5.07/5.25          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 5.07/5.25          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 5.07/5.25          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 5.07/5.25          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 5.07/5.25          | ~ (v1_funct_1 @ X25))),
% 5.07/5.25      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.07/5.25  thf('112', plain,
% 5.07/5.25      ((~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.07/5.25        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 5.07/5.25           (k1_relat_1 @ sk_C))
% 5.07/5.25        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25            != (k2_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['110', '111'])).
% 5.07/5.25  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('114', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['64', '65'])).
% 5.07/5.25  thf('115', plain,
% 5.07/5.25      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['79', '84'])).
% 5.07/5.25  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('117', plain,
% 5.07/5.25      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 5.07/5.25         (k1_relat_1 @ sk_C))
% 5.07/5.25        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 5.07/5.25  thf('118', plain,
% 5.07/5.25      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 5.07/5.25        (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('simplify', [status(thm)], ['117'])).
% 5.07/5.25  thf('119', plain,
% 5.07/5.25      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 5.07/5.25      inference('simplify', [status(thm)], ['97'])).
% 5.07/5.25  thf('120', plain,
% 5.07/5.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.07/5.25         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 5.07/5.25          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 5.07/5.25      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.07/5.25  thf('121', plain,
% 5.07/5.25      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['119', '120'])).
% 5.07/5.25  thf('122', plain,
% 5.07/5.25      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['100', '109', '118', '121'])).
% 5.07/5.25  thf('123', plain,
% 5.07/5.25      (![X4 : $i]:
% 5.07/5.25         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 5.07/5.25          | ~ (v2_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_relat_1 @ X4))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.07/5.25  thf('124', plain,
% 5.07/5.25      (![X4 : $i]:
% 5.07/5.25         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 5.07/5.25          | ~ (v2_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_relat_1 @ X4))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.07/5.25  thf('125', plain,
% 5.07/5.25      (![X4 : $i]:
% 5.07/5.25         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 5.07/5.25          | ~ (v2_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_relat_1 @ X4))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.07/5.25  thf('126', plain,
% 5.07/5.25      (![X4 : $i]:
% 5.07/5.25         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 5.07/5.25          | ~ (v2_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_relat_1 @ X4))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.07/5.25  thf('127', plain,
% 5.07/5.25      (![X6 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X6)
% 5.07/5.25          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 5.07/5.25          | ~ (v1_funct_1 @ X6)
% 5.07/5.25          | ~ (v1_relat_1 @ X6))),
% 5.07/5.25      inference('cnf', [status(esa)], [t65_funct_1])).
% 5.07/5.25  thf(t55_funct_1, axiom,
% 5.07/5.25    (![A:$i]:
% 5.07/5.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.07/5.25       ( ( v2_funct_1 @ A ) =>
% 5.07/5.25         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.07/5.25           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.07/5.25  thf('128', plain,
% 5.07/5.25      (![X5 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X5)
% 5.07/5.25          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 5.07/5.25          | ~ (v1_funct_1 @ X5)
% 5.07/5.25          | ~ (v1_relat_1 @ X5))),
% 5.07/5.25      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.07/5.25  thf('129', plain,
% 5.07/5.25      (![X0 : $i]:
% 5.07/5.25         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 5.07/5.25          | ~ (v1_relat_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.07/5.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.07/5.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 5.07/5.25      inference('sup+', [status(thm)], ['127', '128'])).
% 5.07/5.25  thf('130', plain,
% 5.07/5.25      (![X0 : $i]:
% 5.07/5.25         (~ (v1_relat_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.07/5.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_relat_1 @ X0)
% 5.07/5.25          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['126', '129'])).
% 5.07/5.25  thf('131', plain,
% 5.07/5.25      (![X0 : $i]:
% 5.07/5.25         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 5.07/5.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.07/5.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_relat_1 @ X0))),
% 5.07/5.25      inference('simplify', [status(thm)], ['130'])).
% 5.07/5.25  thf('132', plain,
% 5.07/5.25      (![X0 : $i]:
% 5.07/5.25         (~ (v1_relat_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_relat_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.07/5.25          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['125', '131'])).
% 5.07/5.25  thf('133', plain,
% 5.07/5.25      (![X0 : $i]:
% 5.07/5.25         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 5.07/5.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_relat_1 @ X0))),
% 5.07/5.25      inference('simplify', [status(thm)], ['132'])).
% 5.07/5.25  thf('134', plain,
% 5.07/5.25      (![X0 : $i]:
% 5.07/5.25         (~ (v1_relat_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_relat_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['124', '133'])).
% 5.07/5.25  thf('135', plain,
% 5.07/5.25      (![X0 : $i]:
% 5.07/5.25         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 5.07/5.25          | ~ (v2_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_relat_1 @ X0))),
% 5.07/5.25      inference('simplify', [status(thm)], ['134'])).
% 5.07/5.25  thf('136', plain,
% 5.07/5.25      (![X5 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X5)
% 5.07/5.25          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 5.07/5.25          | ~ (v1_funct_1 @ X5)
% 5.07/5.25          | ~ (v1_relat_1 @ X5))),
% 5.07/5.25      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.07/5.25  thf('137', plain,
% 5.07/5.25      (![X4 : $i]:
% 5.07/5.25         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 5.07/5.25          | ~ (v2_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_relat_1 @ X4))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.07/5.25  thf('138', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf('139', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('140', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('141', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('demod', [status(thm)], ['139', '140'])).
% 5.07/5.25  thf('142', plain,
% 5.07/5.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X25)
% 5.07/5.25          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 5.07/5.25          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 5.07/5.25             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 5.07/5.25          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 5.07/5.25          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 5.07/5.25          | ~ (v1_funct_1 @ X25))),
% 5.07/5.25      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.07/5.25  thf('143', plain,
% 5.07/5.25      ((~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.07/5.25        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25           (k1_zfmisc_1 @ 
% 5.07/5.25            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 5.07/5.25        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25            != (u1_struct_0 @ sk_B))
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['141', '142'])).
% 5.07/5.25  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('145', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('146', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('147', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.07/5.25      inference('demod', [status(thm)], ['145', '146'])).
% 5.07/5.25  thf('148', plain,
% 5.07/5.25      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['27', '28'])).
% 5.07/5.25  thf('149', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('150', plain,
% 5.07/5.25      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['148', '149'])).
% 5.07/5.25  thf('151', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('152', plain,
% 5.07/5.25      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25         (k1_zfmisc_1 @ 
% 5.07/5.25          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 5.07/5.25        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 5.07/5.25      inference('demod', [status(thm)], ['143', '144', '147', '150', '151'])).
% 5.07/5.25  thf('153', plain,
% 5.07/5.25      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B)
% 5.07/5.25        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25           (k1_zfmisc_1 @ 
% 5.07/5.25            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 5.07/5.25      inference('sup-', [status(thm)], ['138', '152'])).
% 5.07/5.25  thf('154', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('155', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('156', plain,
% 5.07/5.25      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 5.07/5.25        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25           (k1_zfmisc_1 @ 
% 5.07/5.25            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 5.07/5.25      inference('demod', [status(thm)], ['153', '154', '155'])).
% 5.07/5.25  thf('157', plain,
% 5.07/5.25      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.07/5.25      inference('simplify', [status(thm)], ['156'])).
% 5.07/5.25  thf('158', plain,
% 5.07/5.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X25)
% 5.07/5.25          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 5.07/5.25          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 5.07/5.25             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 5.07/5.25          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 5.07/5.25          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 5.07/5.25          | ~ (v1_funct_1 @ X25))),
% 5.07/5.25      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.07/5.25  thf('159', plain,
% 5.07/5.25      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25             (k1_relat_1 @ sk_C))
% 5.07/5.25        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_zfmisc_1 @ 
% 5.07/5.25            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.07/5.25        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['157', '158'])).
% 5.07/5.25  thf('160', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.07/5.25      inference('simplify', [status(thm)], ['108'])).
% 5.07/5.25  thf('161', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf('162', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('demod', [status(thm)], ['139', '140'])).
% 5.07/5.25  thf('163', plain,
% 5.07/5.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X25)
% 5.07/5.25          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 5.07/5.25          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 5.07/5.25          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 5.07/5.25          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 5.07/5.25          | ~ (v1_funct_1 @ X25))),
% 5.07/5.25      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.07/5.25  thf('164', plain,
% 5.07/5.25      ((~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.07/5.25        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25           (k1_relat_1 @ sk_C))
% 5.07/5.25        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25            != (u1_struct_0 @ sk_B))
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['162', '163'])).
% 5.07/5.25  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('166', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.07/5.25      inference('demod', [status(thm)], ['145', '146'])).
% 5.07/5.25  thf('167', plain,
% 5.07/5.25      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.07/5.25         = (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['148', '149'])).
% 5.07/5.25  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('169', plain,
% 5.07/5.25      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25         (k1_relat_1 @ sk_C))
% 5.07/5.25        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 5.07/5.25      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 5.07/5.25  thf('170', plain,
% 5.07/5.25      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B)
% 5.07/5.25        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25           (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['161', '169'])).
% 5.07/5.25  thf('171', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('172', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('173', plain,
% 5.07/5.25      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 5.07/5.25        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25           (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['170', '171', '172'])).
% 5.07/5.25  thf('174', plain,
% 5.07/5.25      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25        (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('simplify', [status(thm)], ['173'])).
% 5.07/5.25  thf('175', plain,
% 5.07/5.25      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25         (k1_zfmisc_1 @ 
% 5.07/5.25          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.07/5.25        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['159', '160', '174'])).
% 5.07/5.25  thf('176', plain,
% 5.07/5.25      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.07/5.25      inference('simplify', [status(thm)], ['156'])).
% 5.07/5.25  thf('177', plain,
% 5.07/5.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.07/5.25         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 5.07/5.25          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 5.07/5.25      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.07/5.25  thf('178', plain,
% 5.07/5.25      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['176', '177'])).
% 5.07/5.25  thf('179', plain,
% 5.07/5.25      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25         (k1_zfmisc_1 @ 
% 5.07/5.25          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.07/5.25        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['175', '178'])).
% 5.07/5.25  thf('180', plain,
% 5.07/5.25      ((~ (v1_relat_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C)
% 5.07/5.25        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_zfmisc_1 @ 
% 5.07/5.25            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.07/5.25      inference('sup-', [status(thm)], ['137', '179'])).
% 5.07/5.25  thf('181', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf(cc2_relat_1, axiom,
% 5.07/5.25    (![A:$i]:
% 5.07/5.25     ( ( v1_relat_1 @ A ) =>
% 5.07/5.25       ( ![B:$i]:
% 5.07/5.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.07/5.25  thf('182', plain,
% 5.07/5.25      (![X0 : $i, X1 : $i]:
% 5.07/5.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 5.07/5.25          | (v1_relat_1 @ X0)
% 5.07/5.25          | ~ (v1_relat_1 @ X1))),
% 5.07/5.25      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.07/5.25  thf('183', plain,
% 5.07/5.25      ((~ (v1_relat_1 @ 
% 5.07/5.25           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 5.07/5.25        | (v1_relat_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['181', '182'])).
% 5.07/5.25  thf(fc6_relat_1, axiom,
% 5.07/5.25    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.07/5.25  thf('184', plain,
% 5.07/5.25      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.07/5.25  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['183', '184'])).
% 5.07/5.25  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('187', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('188', plain,
% 5.07/5.25      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_zfmisc_1 @ 
% 5.07/5.25            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.07/5.25      inference('demod', [status(thm)], ['180', '185', '186', '187'])).
% 5.07/5.25  thf('189', plain,
% 5.07/5.25      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v1_relat_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C)
% 5.07/5.25        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_zfmisc_1 @ 
% 5.07/5.25            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.07/5.25      inference('sup-', [status(thm)], ['136', '188'])).
% 5.07/5.25  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['183', '184'])).
% 5.07/5.25  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('193', plain,
% 5.07/5.25      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_zfmisc_1 @ 
% 5.07/5.25            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.07/5.25      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 5.07/5.25  thf('194', plain,
% 5.07/5.25      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('simplify', [status(thm)], ['193'])).
% 5.07/5.25  thf('195', plain,
% 5.07/5.25      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.07/5.25         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 5.07/5.25          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 5.07/5.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.07/5.25  thf('196', plain,
% 5.07/5.25      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25         (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.07/5.25         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.07/5.25      inference('sup-', [status(thm)], ['194', '195'])).
% 5.07/5.25  thf('197', plain,
% 5.07/5.25      (![X6 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X6)
% 5.07/5.25          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 5.07/5.25          | ~ (v1_funct_1 @ X6)
% 5.07/5.25          | ~ (v1_relat_1 @ X6))),
% 5.07/5.25      inference('cnf', [status(esa)], [t65_funct_1])).
% 5.07/5.25  thf('198', plain,
% 5.07/5.25      (![X5 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X5)
% 5.07/5.25          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 5.07/5.25          | ~ (v1_funct_1 @ X5)
% 5.07/5.25          | ~ (v1_relat_1 @ X5))),
% 5.07/5.25      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.07/5.25  thf('199', plain,
% 5.07/5.25      (![X4 : $i]:
% 5.07/5.25         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 5.07/5.25          | ~ (v2_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_funct_1 @ X4)
% 5.07/5.25          | ~ (v1_relat_1 @ X4))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.07/5.25  thf('200', plain,
% 5.07/5.25      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.07/5.25      inference('simplify', [status(thm)], ['156'])).
% 5.07/5.25  thf('201', plain,
% 5.07/5.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.07/5.25         (~ (v2_funct_1 @ X25)
% 5.07/5.25          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 5.07/5.25          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 5.07/5.25          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 5.07/5.25          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 5.07/5.25          | ~ (v1_funct_1 @ X25))),
% 5.07/5.25      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.07/5.25  thf('202', plain,
% 5.07/5.25      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25             (k1_relat_1 @ sk_C))
% 5.07/5.25        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.07/5.25        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['200', '201'])).
% 5.07/5.25  thf('203', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.07/5.25      inference('simplify', [status(thm)], ['108'])).
% 5.07/5.25  thf('204', plain,
% 5.07/5.25      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25        (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('simplify', [status(thm)], ['173'])).
% 5.07/5.25  thf('205', plain,
% 5.07/5.25      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.07/5.25        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['202', '203', '204'])).
% 5.07/5.25  thf('206', plain,
% 5.07/5.25      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['176', '177'])).
% 5.07/5.25  thf('207', plain,
% 5.07/5.25      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.07/5.25        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['205', '206'])).
% 5.07/5.25  thf('208', plain,
% 5.07/5.25      ((~ (v1_relat_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C)
% 5.07/5.25        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['199', '207'])).
% 5.07/5.25  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['183', '184'])).
% 5.07/5.25  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('211', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('212', plain,
% 5.07/5.25      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.07/5.25      inference('demod', [status(thm)], ['208', '209', '210', '211'])).
% 5.07/5.25  thf('213', plain,
% 5.07/5.25      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v1_relat_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C)
% 5.07/5.25        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['198', '212'])).
% 5.07/5.25  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['183', '184'])).
% 5.07/5.25  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('216', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('217', plain,
% 5.07/5.25      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.07/5.25        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.07/5.25      inference('demod', [status(thm)], ['213', '214', '215', '216'])).
% 5.07/5.25  thf('218', plain,
% 5.07/5.25      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25        (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.07/5.25      inference('simplify', [status(thm)], ['217'])).
% 5.07/5.25  thf('219', plain,
% 5.07/5.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.07/5.25         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 5.07/5.25          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 5.07/5.25          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.07/5.25  thf('220', plain,
% 5.07/5.25      ((~ (zip_tseitin_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.07/5.25           (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))
% 5.07/5.25        | ((k1_relat_1 @ sk_C)
% 5.07/5.25            = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25               (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 5.07/5.25      inference('sup-', [status(thm)], ['218', '219'])).
% 5.07/5.25  thf('221', plain,
% 5.07/5.25      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))
% 5.07/5.25        | ~ (v1_relat_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C)
% 5.07/5.25        | ((k1_relat_1 @ sk_C)
% 5.07/5.25            = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25               (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 5.07/5.25      inference('sup-', [status(thm)], ['197', '220'])).
% 5.07/5.25  thf('222', plain,
% 5.07/5.25      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.07/5.25      inference('sup+', [status(thm)], ['11', '12'])).
% 5.07/5.25  thf('223', plain,
% 5.07/5.25      (![X28 : $i]:
% 5.07/5.25         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 5.07/5.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.07/5.25  thf('224', plain,
% 5.07/5.25      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.07/5.25        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['14', '15'])).
% 5.07/5.25  thf('225', plain,
% 5.07/5.25      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.07/5.25        | ~ (l1_struct_0 @ sk_B)
% 5.07/5.25        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['223', '224'])).
% 5.07/5.25  thf('226', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.07/5.25      inference('sup+', [status(thm)], ['29', '30'])).
% 5.07/5.25  thf('227', plain, ((l1_struct_0 @ sk_B)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('228', plain,
% 5.07/5.25      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))
% 5.07/5.25        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.07/5.25      inference('demod', [status(thm)], ['225', '226', '227'])).
% 5.07/5.25  thf('229', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('230', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['33', '40'])).
% 5.07/5.25  thf('231', plain,
% 5.07/5.25      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 5.07/5.25        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['228', '229', '230'])).
% 5.07/5.25  thf('232', plain,
% 5.07/5.25      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 5.07/5.25        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['222', '231'])).
% 5.07/5.25  thf('233', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['38', '39'])).
% 5.07/5.25  thf('234', plain,
% 5.07/5.25      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 5.07/5.25      inference('clc', [status(thm)], ['232', '233'])).
% 5.07/5.25  thf('235', plain, ((v1_relat_1 @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['183', '184'])).
% 5.07/5.25  thf('236', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('237', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('238', plain,
% 5.07/5.25      (((k1_relat_1 @ sk_C)
% 5.07/5.25         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25            (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.07/5.25      inference('demod', [status(thm)], ['221', '234', '235', '236', '237'])).
% 5.07/5.25  thf('239', plain,
% 5.07/5.25      (((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.07/5.25      inference('sup+', [status(thm)], ['196', '238'])).
% 5.07/5.25  thf('240', plain,
% 5.07/5.25      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 5.07/5.25        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('sup+', [status(thm)], ['135', '239'])).
% 5.07/5.25  thf('241', plain,
% 5.07/5.25      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 5.07/5.25      inference('simplify', [status(thm)], ['97'])).
% 5.07/5.25  thf('242', plain,
% 5.07/5.25      (![X0 : $i, X1 : $i]:
% 5.07/5.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 5.07/5.25          | (v1_relat_1 @ X0)
% 5.07/5.25          | ~ (v1_relat_1 @ X1))),
% 5.07/5.25      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.07/5.25  thf('243', plain,
% 5.07/5.25      ((~ (v1_relat_1 @ 
% 5.07/5.25           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 5.07/5.25        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['241', '242'])).
% 5.07/5.25  thf('244', plain,
% 5.07/5.25      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 5.07/5.25      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.07/5.25  thf('245', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['243', '244'])).
% 5.07/5.25  thf('246', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.07/5.25      inference('simplify', [status(thm)], ['108'])).
% 5.07/5.25  thf('247', plain,
% 5.07/5.25      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['240', '245', '246'])).
% 5.07/5.25  thf('248', plain,
% 5.07/5.25      ((~ (v1_relat_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C)
% 5.07/5.25        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 5.07/5.25      inference('sup-', [status(thm)], ['123', '247'])).
% 5.07/5.25  thf('249', plain, ((v1_relat_1 @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['183', '184'])).
% 5.07/5.25  thf('250', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('251', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('252', plain,
% 5.07/5.25      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['248', '249', '250', '251'])).
% 5.07/5.25  thf('253', plain,
% 5.07/5.25      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.07/5.25        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['122', '252'])).
% 5.07/5.25  thf('254', plain,
% 5.07/5.25      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.07/5.25        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.07/5.25      inference('simplify', [status(thm)], ['253'])).
% 5.07/5.25  thf('255', plain,
% 5.07/5.25      ((~ (v1_relat_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C)
% 5.07/5.25        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.07/5.25      inference('sup-', [status(thm)], ['89', '254'])).
% 5.07/5.25  thf('256', plain, ((v1_relat_1 @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['183', '184'])).
% 5.07/5.25  thf('257', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('258', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('259', plain,
% 5.07/5.25      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.07/5.25         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.07/5.25      inference('demod', [status(thm)], ['255', '256', '257', '258'])).
% 5.07/5.25  thf('260', plain,
% 5.07/5.25      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.07/5.25          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['88', '259'])).
% 5.07/5.25  thf('261', plain,
% 5.07/5.25      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.07/5.25           sk_C)
% 5.07/5.25        | ~ (v1_relat_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v2_funct_1 @ sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['0', '260'])).
% 5.07/5.25  thf('262', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('demod', [status(thm)], ['139', '140'])).
% 5.07/5.25  thf('263', plain,
% 5.07/5.25      ((m1_subset_1 @ sk_C @ 
% 5.07/5.25        (k1_zfmisc_1 @ 
% 5.07/5.25         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.07/5.25      inference('demod', [status(thm)], ['139', '140'])).
% 5.07/5.25  thf(reflexivity_r2_funct_2, axiom,
% 5.07/5.25    (![A:$i,B:$i,C:$i,D:$i]:
% 5.07/5.25     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.07/5.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.07/5.25         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.07/5.25         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.07/5.25       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 5.07/5.25  thf('264', plain,
% 5.07/5.25      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 5.07/5.25         ((r2_funct_2 @ X21 @ X22 @ X23 @ X23)
% 5.07/5.25          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 5.07/5.25          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 5.07/5.25          | ~ (v1_funct_1 @ X23)
% 5.07/5.25          | ~ (v1_funct_1 @ X24)
% 5.07/5.25          | ~ (v1_funct_2 @ X24 @ X21 @ X22)
% 5.07/5.25          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.07/5.25      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 5.07/5.25  thf('265', plain,
% 5.07/5.25      (![X0 : $i]:
% 5.07/5.25         (~ (m1_subset_1 @ X0 @ 
% 5.07/5.25             (k1_zfmisc_1 @ 
% 5.07/5.25              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.07/5.25          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.07/5.25          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.07/5.25             sk_C))),
% 5.07/5.25      inference('sup-', [status(thm)], ['263', '264'])).
% 5.07/5.25  thf('266', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('267', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.07/5.25      inference('demod', [status(thm)], ['145', '146'])).
% 5.07/5.25  thf('268', plain,
% 5.07/5.25      (![X0 : $i]:
% 5.07/5.25         (~ (m1_subset_1 @ X0 @ 
% 5.07/5.25             (k1_zfmisc_1 @ 
% 5.07/5.25              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.07/5.25          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.07/5.25          | ~ (v1_funct_1 @ X0)
% 5.07/5.25          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.07/5.25             sk_C))),
% 5.07/5.25      inference('demod', [status(thm)], ['265', '266', '267'])).
% 5.07/5.25  thf('269', plain,
% 5.07/5.25      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 5.07/5.25        | ~ (v1_funct_1 @ sk_C)
% 5.07/5.25        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.07/5.25      inference('sup-', [status(thm)], ['262', '268'])).
% 5.07/5.25  thf('270', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('271', plain,
% 5.07/5.25      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.07/5.25      inference('demod', [status(thm)], ['145', '146'])).
% 5.07/5.25  thf('272', plain,
% 5.07/5.25      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['269', '270', '271'])).
% 5.07/5.25  thf('273', plain, ((v1_relat_1 @ sk_C)),
% 5.07/5.25      inference('demod', [status(thm)], ['183', '184'])).
% 5.07/5.25  thf('274', plain, ((v1_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('275', plain, ((v2_funct_1 @ sk_C)),
% 5.07/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.07/5.25  thf('276', plain, ($false),
% 5.07/5.25      inference('demod', [status(thm)], ['261', '272', '273', '274', '275'])).
% 5.07/5.25  
% 5.07/5.25  % SZS output end Refutation
% 5.07/5.25  
% 5.07/5.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
