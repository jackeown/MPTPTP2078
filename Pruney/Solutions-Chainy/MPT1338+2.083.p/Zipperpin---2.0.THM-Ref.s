%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d763772SWv

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:01 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 375 expanded)
%              Number of leaves         :   43 ( 131 expanded)
%              Depth                    :   15
%              Number of atoms          : 1124 (9603 expanded)
%              Number of equality atoms :   92 ( 536 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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

thf('33',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
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

thf('36',plain,(
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

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('42',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('49',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['46'])).

thf('50',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','47','48','49'])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X25 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['46'])).

thf('57',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('61',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','67','68'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('70',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('71',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','73'])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','74'])).

thf('76',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('78',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('79',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','67','68'])).

thf('81',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','86'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['10','87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d763772SWv
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 369 iterations in 0.509s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.96  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.76/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.96  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.76/0.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.76/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.96  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.76/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.96  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.96  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.76/0.96  thf(t62_tops_2, conjecture,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_struct_0 @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.76/0.96           ( ![C:$i]:
% 0.76/0.96             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.96                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                 ( m1_subset_1 @
% 0.76/0.96                   C @ 
% 0.76/0.96                   ( k1_zfmisc_1 @
% 0.76/0.96                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.96               ( ( ( ( k2_relset_1 @
% 0.76/0.96                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.96                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.96                   ( v2_funct_1 @ C ) ) =>
% 0.76/0.96                 ( ( ( k1_relset_1 @
% 0.76/0.96                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.96                       ( k2_tops_2 @
% 0.76/0.96                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.96                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.96                   ( ( k2_relset_1 @
% 0.76/0.96                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.96                       ( k2_tops_2 @
% 0.76/0.96                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.96                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i]:
% 0.76/0.96        ( ( l1_struct_0 @ A ) =>
% 0.76/0.96          ( ![B:$i]:
% 0.76/0.96            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.76/0.96              ( ![C:$i]:
% 0.76/0.96                ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.96                    ( v1_funct_2 @
% 0.76/0.96                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                    ( m1_subset_1 @
% 0.76/0.96                      C @ 
% 0.76/0.96                      ( k1_zfmisc_1 @
% 0.76/0.96                        ( k2_zfmisc_1 @
% 0.76/0.96                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.96                  ( ( ( ( k2_relset_1 @
% 0.76/0.96                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.96                        ( k2_struct_0 @ B ) ) & 
% 0.76/0.96                      ( v2_funct_1 @ C ) ) =>
% 0.76/0.96                    ( ( ( k1_relset_1 @
% 0.76/0.96                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.96                          ( k2_tops_2 @
% 0.76/0.96                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.96                        ( k2_struct_0 @ B ) ) & 
% 0.76/0.96                      ( ( k2_relset_1 @
% 0.76/0.96                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.96                          ( k2_tops_2 @
% 0.76/0.96                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.96                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k2_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.76/0.96          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.96  thf(fc5_struct_0, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.96       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      (![X21 : $i]:
% 0.76/0.96         (~ (v1_xboole_0 @ (k2_struct_0 @ X21))
% 0.76/0.96          | ~ (l1_struct_0 @ X21)
% 0.76/0.96          | (v2_struct_0 @ X21))),
% 0.76/0.96      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.76/0.96        | (v2_struct_0 @ sk_B)
% 0.76/0.96        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.96  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('8', plain,
% 0.76/0.96      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['6', '7'])).
% 0.76/0.96  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('clc', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf(d3_struct_0, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      (![X20 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('12', plain,
% 0.76/0.96      (![X20 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf(d1_funct_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.96           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.96             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.96         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.96           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.96             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_1, axiom,
% 0.76/0.96    (![B:$i,A:$i]:
% 0.76/0.96     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.96       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      (![X12 : $i, X13 : $i]:
% 0.76/0.96         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.96  thf(zf_stmt_3, axiom,
% 0.76/0.96    (![C:$i,B:$i,A:$i]:
% 0.76/0.96     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.96       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.96  thf(zf_stmt_5, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.96         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.96           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.96             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.96  thf('15', plain,
% 0.76/0.96      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.96         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.76/0.96          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.76/0.96          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.96        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['14', '15'])).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.76/0.96        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['13', '16'])).
% 0.76/0.96  thf('18', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('19', plain,
% 0.76/0.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.96         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.76/0.96          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.76/0.96          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.96  thf('20', plain,
% 0.76/0.96      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.96        | ((u1_struct_0 @ sk_A)
% 0.76/0.96            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.96         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.76/0.96          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k1_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.96  thf('24', plain,
% 0.76/0.96      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.96        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['20', '23'])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.76/0.96        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['17', '24'])).
% 0.76/0.96  thf('26', plain,
% 0.76/0.96      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.76/0.96        | ~ (l1_struct_0 @ sk_B)
% 0.76/0.96        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['12', '25'])).
% 0.76/0.96  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.96  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('29', plain,
% 0.76/0.96      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.76/0.96        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.76/0.96  thf('30', plain,
% 0.76/0.96      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.76/0.96        | ~ (l1_struct_0 @ sk_A)
% 0.76/0.96        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['11', '29'])).
% 0.76/0.96  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.76/0.96        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['30', '31'])).
% 0.76/0.96  thf('33', plain,
% 0.76/0.96      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_B))
% 0.76/0.96        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96            != (k2_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('34', plain,
% 0.76/0.96      (![X20 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('35', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(d4_tops_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.76/0.96         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.76/0.96  thf('36', plain,
% 0.76/0.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.76/0.96          | ~ (v2_funct_1 @ X24)
% 0.76/0.96          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.76/0.96          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.76/0.96          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.76/0.96          | ~ (v1_funct_1 @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.96        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96            = (k2_funct_1 @ sk_C))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.96        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96            != (u1_struct_0 @ sk_B)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.96  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('39', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('40', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('41', plain,
% 0.76/0.96      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.96  thf('42', plain,
% 0.76/0.96      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96          = (k2_funct_1 @ sk_C))
% 0.76/0.96        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.76/0.96      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.76/0.96  thf('43', plain,
% 0.76/0.96      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.76/0.96        | ~ (l1_struct_0 @ sk_B)
% 0.76/0.96        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96            = (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['34', '42'])).
% 0.76/0.96  thf('44', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.96  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('46', plain,
% 0.76/0.96      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.76/0.96        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96            = (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.76/0.96  thf('47', plain,
% 0.76/0.96      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('simplify', [status(thm)], ['46'])).
% 0.76/0.96  thf('48', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.96  thf('49', plain,
% 0.76/0.96      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('simplify', [status(thm)], ['46'])).
% 0.76/0.96  thf('50', plain,
% 0.76/0.96      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.76/0.96        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['33', '47', '48', '49'])).
% 0.76/0.96  thf('51', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(dt_k2_tops_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.76/0.96         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.76/0.96         ( m1_subset_1 @
% 0.76/0.96           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.76/0.96           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.76/0.96  thf('52', plain,
% 0.76/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.96         ((m1_subset_1 @ (k2_tops_2 @ X25 @ X26 @ X27) @ 
% 0.76/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.76/0.96          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.76/0.96          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.76/0.96          | ~ (v1_funct_1 @ X27))),
% 0.76/0.96      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.76/0.96  thf('53', plain,
% 0.76/0.96      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.96        | (m1_subset_1 @ 
% 0.76/0.96           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.76/0.96           (k1_zfmisc_1 @ 
% 0.76/0.96            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['51', '52'])).
% 0.76/0.96  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('55', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('56', plain,
% 0.76/0.96      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('simplify', [status(thm)], ['46'])).
% 0.76/0.96  thf('57', plain,
% 0.76/0.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.76/0.96      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.76/0.96  thf('58', plain,
% 0.76/0.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.96         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.76/0.96          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.96  thf('59', plain,
% 0.76/0.96      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['57', '58'])).
% 0.76/0.96  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(d9_funct_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.96       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.76/0.96  thf('61', plain,
% 0.76/0.96      (![X5 : $i]:
% 0.76/0.96         (~ (v2_funct_1 @ X5)
% 0.76/0.96          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.76/0.96          | ~ (v1_funct_1 @ X5)
% 0.76/0.96          | ~ (v1_relat_1 @ X5))),
% 0.76/0.96      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.76/0.96  thf('62', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.96        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['60', '61'])).
% 0.76/0.96  thf('63', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(cc2_relat_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.96  thf('64', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.76/0.96          | (v1_relat_1 @ X0)
% 0.76/0.96          | ~ (v1_relat_1 @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.96  thf('65', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ 
% 0.76/0.96           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.76/0.96        | (v1_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['63', '64'])).
% 0.76/0.96  thf(fc6_relat_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.96  thf('66', plain,
% 0.76/0.96      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.76/0.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.96  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('demod', [status(thm)], ['65', '66'])).
% 0.76/0.96  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('69', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['62', '67', '68'])).
% 0.76/0.96  thf(t37_relat_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ A ) =>
% 0.76/0.96       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.76/0.96         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.76/0.96  thf('70', plain,
% 0.76/0.96      (![X4 : $i]:
% 0.76/0.96         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.76/0.96          | ~ (v1_relat_1 @ X4))),
% 0.76/0.96      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.76/0.96  thf('71', plain,
% 0.76/0.96      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.76/0.96        | ~ (v1_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup+', [status(thm)], ['69', '70'])).
% 0.76/0.96  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('demod', [status(thm)], ['65', '66'])).
% 0.76/0.96  thf('73', plain,
% 0.76/0.96      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['71', '72'])).
% 0.76/0.96  thf('74', plain,
% 0.76/0.96      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['59', '73'])).
% 0.76/0.96  thf('75', plain,
% 0.76/0.96      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.76/0.96        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['50', '74'])).
% 0.76/0.96  thf('76', plain,
% 0.76/0.96      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('simplify', [status(thm)], ['75'])).
% 0.76/0.96  thf('77', plain,
% 0.76/0.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.76/0.96      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.76/0.96  thf('78', plain,
% 0.76/0.96      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.76/0.96          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.96  thf('79', plain,
% 0.76/0.96      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['77', '78'])).
% 0.76/0.96  thf('80', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['62', '67', '68'])).
% 0.76/0.96  thf('81', plain,
% 0.76/0.96      (![X4 : $i]:
% 0.76/0.96         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.76/0.96          | ~ (v1_relat_1 @ X4))),
% 0.76/0.96      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.76/0.96  thf('82', plain,
% 0.76/0.96      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.76/0.96        | ~ (v1_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup+', [status(thm)], ['80', '81'])).
% 0.76/0.96  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('demod', [status(thm)], ['65', '66'])).
% 0.76/0.96  thf('84', plain,
% 0.76/0.96      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['82', '83'])).
% 0.76/0.96  thf('85', plain,
% 0.76/0.96      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['79', '84'])).
% 0.76/0.96  thf('86', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['76', '85'])).
% 0.76/0.96  thf('87', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.76/0.96      inference('simplify_reflect-', [status(thm)], ['32', '86'])).
% 0.76/0.96  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.96  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.96      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.96  thf('89', plain, ($false),
% 0.76/0.96      inference('demod', [status(thm)], ['10', '87', '88'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
