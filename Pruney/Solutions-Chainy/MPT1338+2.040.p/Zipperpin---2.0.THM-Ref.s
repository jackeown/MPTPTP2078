%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MX1HHUkCDr

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:53 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 634 expanded)
%              Number of leaves         :   42 ( 200 expanded)
%              Depth                    :   17
%              Number of atoms          : 1754 (16967 expanded)
%              Number of equality atoms :  143 ( 948 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
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

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
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
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X21 @ X23 )
       != X21 )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_tops_2 @ X22 @ X21 @ X23 )
        = ( k2_funct_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('36',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('41',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('55',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('63',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('64',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X21 @ X23 )
       != X21 )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_tops_2 @ X22 @ X21 @ X23 )
        = ( k2_funct_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('86',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','86'])).

thf('88',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','72','88'])).

thf('90',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('91',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('93',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('98',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','99'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('102',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('104',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','104'])).

thf('106',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','72','88'])).

thf('108',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('109',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','99'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('112',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','114'])).

thf('116',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['87'])).

thf('117',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('119',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('120',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('128',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('129',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126','127','128'])).

thf('130',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','129'])).

thf('131',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','130'])).

thf('132',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('134',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['132','133'])).

thf('135',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['106','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','135'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('137',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['10','136','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MX1HHUkCDr
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.83/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.03  % Solved by: fo/fo7.sh
% 0.83/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.03  % done 366 iterations in 0.550s
% 0.83/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.03  % SZS output start Refutation
% 0.83/1.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.83/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.03  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.83/1.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.83/1.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.83/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.83/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.83/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.03  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.83/1.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.83/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.83/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.04  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.83/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.83/1.04  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.83/1.04  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.83/1.04  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.04  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.83/1.04  thf(t62_tops_2, conjecture,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( l1_struct_0 @ A ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.83/1.04           ( ![C:$i]:
% 0.83/1.04             ( ( ( v1_funct_1 @ C ) & 
% 0.83/1.04                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.04                 ( m1_subset_1 @
% 0.83/1.04                   C @ 
% 0.83/1.04                   ( k1_zfmisc_1 @
% 0.83/1.04                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.04               ( ( ( ( k2_relset_1 @
% 0.83/1.04                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/1.04                     ( k2_struct_0 @ B ) ) & 
% 0.83/1.04                   ( v2_funct_1 @ C ) ) =>
% 0.83/1.04                 ( ( ( k1_relset_1 @
% 0.83/1.04                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.04                       ( k2_tops_2 @
% 0.83/1.04                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/1.04                     ( k2_struct_0 @ B ) ) & 
% 0.83/1.04                   ( ( k2_relset_1 @
% 0.83/1.04                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.04                       ( k2_tops_2 @
% 0.83/1.04                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/1.04                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.83/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.04    (~( ![A:$i]:
% 0.83/1.04        ( ( l1_struct_0 @ A ) =>
% 0.83/1.04          ( ![B:$i]:
% 0.83/1.04            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.83/1.04              ( ![C:$i]:
% 0.83/1.04                ( ( ( v1_funct_1 @ C ) & 
% 0.83/1.04                    ( v1_funct_2 @
% 0.83/1.04                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.04                    ( m1_subset_1 @
% 0.83/1.04                      C @ 
% 0.83/1.04                      ( k1_zfmisc_1 @
% 0.83/1.04                        ( k2_zfmisc_1 @
% 0.83/1.04                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.04                  ( ( ( ( k2_relset_1 @
% 0.83/1.04                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/1.04                        ( k2_struct_0 @ B ) ) & 
% 0.83/1.04                      ( v2_funct_1 @ C ) ) =>
% 0.83/1.04                    ( ( ( k1_relset_1 @
% 0.83/1.04                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.04                          ( k2_tops_2 @
% 0.83/1.04                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/1.04                        ( k2_struct_0 @ B ) ) & 
% 0.83/1.04                      ( ( k2_relset_1 @
% 0.83/1.04                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.04                          ( k2_tops_2 @
% 0.83/1.04                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.83/1.04                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.83/1.04    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.83/1.04  thf('0', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(redefinition_k2_relset_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.04       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.83/1.04  thf('1', plain,
% 0.83/1.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.83/1.04         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.83/1.04          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.04  thf('2', plain,
% 0.83/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_relat_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['0', '1'])).
% 0.83/1.04  thf('3', plain,
% 0.83/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf(fc5_struct_0, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.83/1.04       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.83/1.04  thf('5', plain,
% 0.83/1.04      (![X20 : $i]:
% 0.83/1.04         (~ (v1_xboole_0 @ (k2_struct_0 @ X20))
% 0.83/1.04          | ~ (l1_struct_0 @ X20)
% 0.83/1.04          | (v2_struct_0 @ X20))),
% 0.83/1.04      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.83/1.04  thf('6', plain,
% 0.83/1.04      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.83/1.04        | (v2_struct_0 @ sk_B)
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.04  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('8', plain,
% 0.83/1.04      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['6', '7'])).
% 0.83/1.04  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.83/1.04      inference('clc', [status(thm)], ['8', '9'])).
% 0.83/1.04  thf(d3_struct_0, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.83/1.04  thf('11', plain,
% 0.83/1.04      (![X19 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('12', plain,
% 0.83/1.04      (![X19 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf(d1_funct_2, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.04       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.83/1.04           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.83/1.04             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.83/1.04         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.83/1.04           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.83/1.04             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.83/1.04  thf(zf_stmt_1, axiom,
% 0.83/1.04    (![B:$i,A:$i]:
% 0.83/1.04     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.83/1.04       ( zip_tseitin_0 @ B @ A ) ))).
% 0.83/1.04  thf('13', plain,
% 0.83/1.04      (![X11 : $i, X12 : $i]:
% 0.83/1.04         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.83/1.04  thf('14', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.83/1.04  thf(zf_stmt_3, axiom,
% 0.83/1.04    (![C:$i,B:$i,A:$i]:
% 0.83/1.04     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.83/1.04       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.83/1.04  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.83/1.04  thf(zf_stmt_5, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.04       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.83/1.04         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.83/1.04           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.83/1.04             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.83/1.04  thf('15', plain,
% 0.83/1.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.83/1.04         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.83/1.04          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.83/1.04          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.83/1.04  thf('16', plain,
% 0.83/1.04      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/1.04        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['14', '15'])).
% 0.83/1.04  thf('17', plain,
% 0.83/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['13', '16'])).
% 0.83/1.04  thf('18', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('19', plain,
% 0.83/1.04      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.04         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.83/1.04          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.83/1.04          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.83/1.04  thf('20', plain,
% 0.83/1.04      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/1.04        | ((u1_struct_0 @ sk_A)
% 0.83/1.04            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['18', '19'])).
% 0.83/1.04  thf('21', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(redefinition_k1_relset_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.04       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.83/1.04  thf('22', plain,
% 0.83/1.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.04         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.83/1.04          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.83/1.04  thf('23', plain,
% 0.83/1.04      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k1_relat_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['21', '22'])).
% 0.83/1.04  thf('24', plain,
% 0.83/1.04      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.83/1.04        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.83/1.04      inference('demod', [status(thm)], ['20', '23'])).
% 0.83/1.04  thf('25', plain,
% 0.83/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['17', '24'])).
% 0.83/1.04  thf('26', plain,
% 0.83/1.04      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B)
% 0.83/1.04        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['12', '25'])).
% 0.83/1.04  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('29', plain,
% 0.83/1.04      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.83/1.04        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.83/1.04      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.83/1.04  thf('30', plain,
% 0.83/1.04      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_A)
% 0.83/1.04        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['11', '29'])).
% 0.83/1.04  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('32', plain,
% 0.83/1.04      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.83/1.04        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.83/1.04      inference('demod', [status(thm)], ['30', '31'])).
% 0.83/1.04  thf('33', plain,
% 0.83/1.04      (![X19 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('34', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(d4_tops_2, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.04       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.83/1.04         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.83/1.04  thf('35', plain,
% 0.83/1.04      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.04         (((k2_relset_1 @ X22 @ X21 @ X23) != (X21))
% 0.83/1.04          | ~ (v2_funct_1 @ X23)
% 0.83/1.04          | ((k2_tops_2 @ X22 @ X21 @ X23) = (k2_funct_1 @ X23))
% 0.83/1.04          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.83/1.04          | ~ (v1_funct_2 @ X23 @ X22 @ X21)
% 0.83/1.04          | ~ (v1_funct_1 @ X23))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.83/1.04  thf('36', plain,
% 0.83/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/1.04        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04            = (k2_funct_1 @ sk_C))
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.04        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04            != (u1_struct_0 @ sk_B)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.04  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('38', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('40', plain,
% 0.83/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_relat_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['0', '1'])).
% 0.83/1.04  thf('41', plain,
% 0.83/1.04      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04          = (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.83/1.04      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.83/1.04  thf('42', plain,
% 0.83/1.04      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B)
% 0.83/1.04        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04            = (k2_funct_1 @ sk_C)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['33', '41'])).
% 0.83/1.04  thf('43', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('45', plain,
% 0.83/1.04      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.83/1.04        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04            = (k2_funct_1 @ sk_C)))),
% 0.83/1.04      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.83/1.04  thf('46', plain,
% 0.83/1.04      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('simplify', [status(thm)], ['45'])).
% 0.83/1.04  thf('47', plain,
% 0.83/1.04      (![X19 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('48', plain,
% 0.83/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          != (k2_struct_0 @ sk_B))
% 0.83/1.04        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04            != (k2_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('49', plain,
% 0.83/1.04      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          != (k2_struct_0 @ sk_A)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_A))))),
% 0.83/1.04      inference('split', [status(esa)], ['48'])).
% 0.83/1.04  thf('50', plain,
% 0.83/1.04      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04           != (k2_struct_0 @ sk_A))
% 0.83/1.04         | ~ (l1_struct_0 @ sk_B)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_A))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['47', '49'])).
% 0.83/1.04  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('52', plain,
% 0.83/1.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          != (k2_struct_0 @ sk_A)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_A))))),
% 0.83/1.04      inference('demod', [status(thm)], ['50', '51'])).
% 0.83/1.04  thf('53', plain,
% 0.83/1.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_A))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['46', '52'])).
% 0.83/1.04  thf('54', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('55', plain,
% 0.83/1.04      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_A))))),
% 0.83/1.04      inference('demod', [status(thm)], ['53', '54'])).
% 0.83/1.04  thf('56', plain,
% 0.83/1.04      (![X19 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('57', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('58', plain,
% 0.83/1.04      (((m1_subset_1 @ sk_C @ 
% 0.83/1.04         (k1_zfmisc_1 @ 
% 0.83/1.04          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['56', '57'])).
% 0.83/1.04  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('60', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('demod', [status(thm)], ['58', '59'])).
% 0.83/1.04  thf('61', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('62', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.83/1.04      inference('demod', [status(thm)], ['60', '61'])).
% 0.83/1.04  thf(dt_k2_tops_2, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.04       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.83/1.04         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.83/1.04         ( m1_subset_1 @
% 0.83/1.04           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.83/1.04           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.83/1.04  thf('63', plain,
% 0.83/1.04      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.04         ((m1_subset_1 @ (k2_tops_2 @ X24 @ X25 @ X26) @ 
% 0.83/1.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.83/1.04          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.83/1.04          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.83/1.04          | ~ (v1_funct_1 @ X26))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.83/1.04  thf('64', plain,
% 0.83/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.83/1.04        | (m1_subset_1 @ 
% 0.83/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.83/1.04           (k1_zfmisc_1 @ 
% 0.83/1.04            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['62', '63'])).
% 0.83/1.04  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('66', plain,
% 0.83/1.04      (![X19 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('67', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('68', plain,
% 0.83/1.04      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['66', '67'])).
% 0.83/1.04  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('70', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['68', '69'])).
% 0.83/1.04  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('72', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['70', '71'])).
% 0.83/1.04  thf('73', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.83/1.04      inference('demod', [status(thm)], ['60', '61'])).
% 0.83/1.04  thf('74', plain,
% 0.83/1.04      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.04         (((k2_relset_1 @ X22 @ X21 @ X23) != (X21))
% 0.83/1.04          | ~ (v2_funct_1 @ X23)
% 0.83/1.04          | ((k2_tops_2 @ X22 @ X21 @ X23) = (k2_funct_1 @ X23))
% 0.83/1.04          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.83/1.04          | ~ (v1_funct_2 @ X23 @ X22 @ X21)
% 0.83/1.04          | ~ (v1_funct_1 @ X23))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.83/1.04  thf('75', plain,
% 0.83/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.83/1.04        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.04            = (k2_funct_1 @ sk_C))
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.04        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.04            != (k2_relat_1 @ sk_C)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['73', '74'])).
% 0.83/1.04  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('77', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['70', '71'])).
% 0.83/1.04  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('79', plain,
% 0.83/1.04      (![X19 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('80', plain,
% 0.83/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('81', plain,
% 0.83/1.04      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04          = (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['79', '80'])).
% 0.83/1.04  thf('82', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('83', plain,
% 0.83/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['81', '82'])).
% 0.83/1.04  thf('84', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('85', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('86', plain,
% 0.83/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.04         = (k2_relat_1 @ sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.83/1.04  thf('87', plain,
% 0.83/1.04      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.04          = (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.83/1.04      inference('demod', [status(thm)], ['75', '76', '77', '78', '86'])).
% 0.83/1.04  thf('88', plain,
% 0.83/1.04      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.04         = (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('simplify', [status(thm)], ['87'])).
% 0.83/1.04  thf('89', plain,
% 0.83/1.04      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.83/1.04      inference('demod', [status(thm)], ['64', '65', '72', '88'])).
% 0.83/1.04  thf('90', plain,
% 0.83/1.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.83/1.04         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.83/1.04          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.04  thf('91', plain,
% 0.83/1.04      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['89', '90'])).
% 0.83/1.04  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(d9_funct_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.83/1.04       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.83/1.04  thf('93', plain,
% 0.83/1.04      (![X1 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X1)
% 0.83/1.04          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.83/1.04          | ~ (v1_funct_1 @ X1)
% 0.83/1.04          | ~ (v1_relat_1 @ X1))),
% 0.83/1.04      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.83/1.04  thf('94', plain,
% 0.83/1.04      ((~ (v1_relat_1 @ sk_C)
% 0.83/1.04        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['92', '93'])).
% 0.83/1.04  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('96', plain,
% 0.83/1.04      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.83/1.04      inference('demod', [status(thm)], ['94', '95'])).
% 0.83/1.04  thf('97', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(cc1_relset_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.04       ( v1_relat_1 @ C ) ))).
% 0.83/1.04  thf('98', plain,
% 0.83/1.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.83/1.04         ((v1_relat_1 @ X2)
% 0.83/1.04          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.83/1.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.83/1.04  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['97', '98'])).
% 0.83/1.04  thf('100', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['96', '99'])).
% 0.83/1.04  thf(t37_relat_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( v1_relat_1 @ A ) =>
% 0.83/1.04       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.83/1.04         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.83/1.04  thf('101', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.83/1.04  thf('102', plain,
% 0.83/1.04      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C))),
% 0.83/1.04      inference('sup+', [status(thm)], ['100', '101'])).
% 0.83/1.04  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['97', '98'])).
% 0.83/1.04  thf('104', plain,
% 0.83/1.04      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.04      inference('demod', [status(thm)], ['102', '103'])).
% 0.83/1.04  thf('105', plain,
% 0.83/1.04      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['91', '104'])).
% 0.83/1.04  thf('106', plain,
% 0.83/1.04      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_A))))),
% 0.83/1.04      inference('demod', [status(thm)], ['55', '105'])).
% 0.83/1.04  thf('107', plain,
% 0.83/1.04      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.83/1.04      inference('demod', [status(thm)], ['64', '65', '72', '88'])).
% 0.83/1.04  thf('108', plain,
% 0.83/1.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.04         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.83/1.04          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.83/1.04  thf('109', plain,
% 0.83/1.04      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['107', '108'])).
% 0.83/1.04  thf('110', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['96', '99'])).
% 0.83/1.04  thf('111', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.83/1.04  thf('112', plain,
% 0.83/1.04      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C))),
% 0.83/1.04      inference('sup+', [status(thm)], ['110', '111'])).
% 0.83/1.04  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['97', '98'])).
% 0.83/1.04  thf('114', plain,
% 0.83/1.04      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.04      inference('demod', [status(thm)], ['112', '113'])).
% 0.83/1.04  thf('115', plain,
% 0.83/1.04      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['109', '114'])).
% 0.83/1.04  thf('116', plain,
% 0.83/1.04      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.83/1.04         = (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('simplify', [status(thm)], ['87'])).
% 0.83/1.04  thf('117', plain,
% 0.83/1.04      (![X19 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('118', plain,
% 0.83/1.04      (![X19 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('119', plain,
% 0.83/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          != (k2_struct_0 @ sk_B)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('split', [status(esa)], ['48'])).
% 0.83/1.04  thf('120', plain,
% 0.83/1.04      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04           != (k2_struct_0 @ sk_B))
% 0.83/1.04         | ~ (l1_struct_0 @ sk_B)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['118', '119'])).
% 0.83/1.04  thf('121', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('122', plain,
% 0.83/1.04      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          != (k2_struct_0 @ sk_B)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('demod', [status(thm)], ['120', '121'])).
% 0.83/1.04  thf('123', plain,
% 0.83/1.04      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04           != (k2_struct_0 @ sk_B))
% 0.83/1.04         | ~ (l1_struct_0 @ sk_B)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['117', '122'])).
% 0.83/1.04  thf('124', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('125', plain,
% 0.83/1.04      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          != (k2_struct_0 @ sk_B)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('demod', [status(thm)], ['123', '124'])).
% 0.83/1.04  thf('126', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('127', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('128', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('129', plain,
% 0.83/1.04      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.83/1.04          != (k2_relat_1 @ sk_C)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('demod', [status(thm)], ['125', '126', '127', '128'])).
% 0.83/1.04  thf('130', plain,
% 0.83/1.04      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['116', '129'])).
% 0.83/1.04  thf('131', plain,
% 0.83/1.04      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.83/1.04         <= (~
% 0.83/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04                = (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['115', '130'])).
% 0.83/1.04  thf('132', plain,
% 0.83/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          = (k2_struct_0 @ sk_B)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['131'])).
% 0.83/1.04  thf('133', plain,
% 0.83/1.04      (~
% 0.83/1.04       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          = (k2_struct_0 @ sk_A))) | 
% 0.83/1.04       ~
% 0.83/1.04       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          = (k2_struct_0 @ sk_B)))),
% 0.83/1.04      inference('split', [status(esa)], ['48'])).
% 0.83/1.04  thf('134', plain,
% 0.83/1.04      (~
% 0.83/1.04       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.83/1.04          = (k2_struct_0 @ sk_A)))),
% 0.83/1.04      inference('sat_resolution*', [status(thm)], ['132', '133'])).
% 0.83/1.04  thf('135', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('simpl_trail', [status(thm)], ['106', '134'])).
% 0.83/1.04  thf('136', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.83/1.04      inference('simplify_reflect-', [status(thm)], ['32', '135'])).
% 0.83/1.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.83/1.04  thf('137', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.04  thf('138', plain, ($false),
% 0.83/1.04      inference('demod', [status(thm)], ['10', '136', '137'])).
% 0.83/1.04  
% 0.83/1.04  % SZS output end Refutation
% 0.83/1.04  
% 0.83/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
