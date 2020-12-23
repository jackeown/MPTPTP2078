%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWuIxry4tB

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:23 EST 2020

% Result     : Theorem 3.80s
% Output     : Refutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  318 (6444 expanded)
%              Number of leaves         :   45 (1922 expanded)
%              Depth                    :   35
%              Number of atoms          : 3101 (140096 expanded)
%              Number of equality atoms :  172 (5008 expanded)
%              Maximal formula depth    :   17 (   6 average)

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
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

thf('2',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('35',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('37',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

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

thf('46',plain,(
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

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('67',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('73',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','57','58','76'])).

thf('78',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','28','33','34','35','36','78'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

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

thf('82',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
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

thf('91',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('93',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('97',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('102',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('107',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('111',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('112',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','100','109','112'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('114',plain,(
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

thf('115',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('116',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('117',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('128',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('129',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123','126','129','130'])).

thf('132',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['117','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('134',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('140',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('142',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('143',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('146',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144','145','146','147'])).

thf('149',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','148'])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('151',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139','153'])).

thf('155',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('156',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('157',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','157'])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['116','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('163',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['159','164','165','166'])).

thf('168',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['115','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['162','163'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('175',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_funct_2 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['173','179'])).

thf('181',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('182',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('183',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('184',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('185',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('187',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('188',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('190',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['182','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['162','163'])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['181','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['162','163'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['196','197','198','199'])).

thf('201',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('203',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('204',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('205',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('206',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('208',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('209',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('211',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['203','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['162','163'])).

thf('214',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['212','213','214','215'])).

thf('217',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['202','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['162','163'])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('222',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['180','201','222'])).

thf('224',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['114','223'])).

thf('225',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('226',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_funct_2 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('227',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_funct_2 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['225','227'])).

thf('229',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['162','163'])).

thf('233',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','231','232','233','234'])).

thf('236',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('237',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','231','232','233','234'])).

thf('238',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('239',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('240',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('241',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('242',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,(
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
    inference('sup-',[status(thm)],['240','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
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
    inference('sup-',[status(thm)],['239','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['238','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['237','249'])).

thf('251',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('253',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('255',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('257',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['250','255','256'])).

thf('258',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['236','257'])).

thf('259',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['162','163'])).

thf('260',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['258','259','260','261'])).

thf('263',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['113','235','262'])).

thf('264',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['80','264'])).

thf('266',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['162','163'])).

thf('267',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['265','266','267','268'])).

thf('270',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('271',plain,(
    $false ),
    inference(demod,[status(thm)],['79','269','270'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWuIxry4tB
% 0.17/0.38  % Computer   : n022.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 12:04:11 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 3.80/4.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.80/4.01  % Solved by: fo/fo7.sh
% 3.80/4.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.80/4.01  % done 1089 iterations in 3.514s
% 3.80/4.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.80/4.01  % SZS output start Refutation
% 3.80/4.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.80/4.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.80/4.01  thf(sk_A_type, type, sk_A: $i).
% 3.80/4.01  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.80/4.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.80/4.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.80/4.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.80/4.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.80/4.01  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.80/4.01  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.80/4.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.80/4.01  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.80/4.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.80/4.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.80/4.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.80/4.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.80/4.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.80/4.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.80/4.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.80/4.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.80/4.01  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 3.80/4.01  thf(sk_B_type, type, sk_B: $i).
% 3.80/4.01  thf(sk_C_type, type, sk_C: $i).
% 3.80/4.01  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 3.80/4.01  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.80/4.01  thf(d3_struct_0, axiom,
% 3.80/4.01    (![A:$i]:
% 3.80/4.01     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.80/4.01  thf('0', plain,
% 3.80/4.01      (![X28 : $i]:
% 3.80/4.01         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 3.80/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.01  thf('1', plain,
% 3.80/4.01      (![X28 : $i]:
% 3.80/4.01         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 3.80/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.01  thf(t64_tops_2, conjecture,
% 3.80/4.01    (![A:$i]:
% 3.80/4.01     ( ( l1_struct_0 @ A ) =>
% 3.80/4.01       ( ![B:$i]:
% 3.80/4.01         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.80/4.01           ( ![C:$i]:
% 3.80/4.01             ( ( ( v1_funct_1 @ C ) & 
% 3.80/4.01                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.80/4.01                 ( m1_subset_1 @
% 3.80/4.01                   C @ 
% 3.80/4.01                   ( k1_zfmisc_1 @
% 3.80/4.01                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.80/4.01               ( ( ( ( k2_relset_1 @
% 3.80/4.01                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.80/4.01                     ( k2_struct_0 @ B ) ) & 
% 3.80/4.01                   ( v2_funct_1 @ C ) ) =>
% 3.80/4.01                 ( r2_funct_2 @
% 3.80/4.01                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.80/4.01                   ( k2_tops_2 @
% 3.80/4.01                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.80/4.01                     ( k2_tops_2 @
% 3.80/4.01                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 3.80/4.01                   C ) ) ) ) ) ) ))).
% 3.80/4.01  thf(zf_stmt_0, negated_conjecture,
% 3.80/4.01    (~( ![A:$i]:
% 3.80/4.01        ( ( l1_struct_0 @ A ) =>
% 3.80/4.01          ( ![B:$i]:
% 3.80/4.01            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.80/4.01              ( ![C:$i]:
% 3.80/4.01                ( ( ( v1_funct_1 @ C ) & 
% 3.80/4.01                    ( v1_funct_2 @
% 3.80/4.01                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.80/4.01                    ( m1_subset_1 @
% 3.80/4.01                      C @ 
% 3.80/4.01                      ( k1_zfmisc_1 @
% 3.80/4.01                        ( k2_zfmisc_1 @
% 3.80/4.01                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.80/4.01                  ( ( ( ( k2_relset_1 @
% 3.80/4.01                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.80/4.01                        ( k2_struct_0 @ B ) ) & 
% 3.80/4.01                      ( v2_funct_1 @ C ) ) =>
% 3.80/4.01                    ( r2_funct_2 @
% 3.80/4.01                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.80/4.01                      ( k2_tops_2 @
% 3.80/4.01                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.80/4.01                        ( k2_tops_2 @
% 3.80/4.01                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 3.80/4.01                      C ) ) ) ) ) ) ) )),
% 3.80/4.01    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 3.80/4.01  thf('2', plain,
% 3.80/4.01      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.01          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.01           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 3.80/4.01          sk_C)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('3', plain,
% 3.80/4.01      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.01           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.01            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.80/4.01           sk_C)
% 3.80/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup-', [status(thm)], ['1', '2'])).
% 3.80/4.01  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('5', plain,
% 3.80/4.01      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.01          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.01           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.80/4.01          sk_C)),
% 3.80/4.01      inference('demod', [status(thm)], ['3', '4'])).
% 3.80/4.01  thf('6', plain,
% 3.80/4.01      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.01           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.01            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.80/4.01           sk_C)
% 3.80/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup-', [status(thm)], ['0', '5'])).
% 3.80/4.01  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('8', plain,
% 3.80/4.01      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.01          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.80/4.01           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 3.80/4.01          sk_C)),
% 3.80/4.01      inference('demod', [status(thm)], ['6', '7'])).
% 3.80/4.01  thf(d1_funct_2, axiom,
% 3.80/4.01    (![A:$i,B:$i,C:$i]:
% 3.80/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.01       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.80/4.01           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.80/4.01             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.80/4.01         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.80/4.01           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.80/4.01             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.80/4.01  thf(zf_stmt_1, axiom,
% 3.80/4.01    (![B:$i,A:$i]:
% 3.80/4.01     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.80/4.01       ( zip_tseitin_0 @ B @ A ) ))).
% 3.80/4.01  thf('9', plain,
% 3.80/4.01      (![X13 : $i, X14 : $i]:
% 3.80/4.01         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.80/4.01  thf('10', plain,
% 3.80/4.01      ((m1_subset_1 @ sk_C @ 
% 3.80/4.01        (k1_zfmisc_1 @ 
% 3.80/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.80/4.01  thf(zf_stmt_3, axiom,
% 3.80/4.01    (![C:$i,B:$i,A:$i]:
% 3.80/4.01     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.80/4.01       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.80/4.01  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.80/4.01  thf(zf_stmt_5, axiom,
% 3.80/4.01    (![A:$i,B:$i,C:$i]:
% 3.80/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.01       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.80/4.01         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.80/4.01           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.80/4.01             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.80/4.01  thf('11', plain,
% 3.80/4.01      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.80/4.01         (~ (zip_tseitin_0 @ X18 @ X19)
% 3.80/4.01          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 3.80/4.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.80/4.01  thf('12', plain,
% 3.80/4.01      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.80/4.01        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.80/4.01      inference('sup-', [status(thm)], ['10', '11'])).
% 3.80/4.01  thf('13', plain,
% 3.80/4.01      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.80/4.01        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.80/4.01      inference('sup-', [status(thm)], ['9', '12'])).
% 3.80/4.01  thf('14', plain,
% 3.80/4.01      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('15', plain,
% 3.80/4.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.80/4.01         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 3.80/4.01          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 3.80/4.01          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.80/4.01  thf('16', plain,
% 3.80/4.01      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.80/4.01        | ((u1_struct_0 @ sk_A)
% 3.80/4.01            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 3.80/4.01      inference('sup-', [status(thm)], ['14', '15'])).
% 3.80/4.01  thf('17', plain,
% 3.80/4.01      ((m1_subset_1 @ sk_C @ 
% 3.80/4.01        (k1_zfmisc_1 @ 
% 3.80/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf(redefinition_k1_relset_1, axiom,
% 3.80/4.01    (![A:$i,B:$i,C:$i]:
% 3.80/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.01       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.80/4.01  thf('18', plain,
% 3.80/4.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.80/4.01         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 3.80/4.01          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.80/4.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.80/4.01  thf('19', plain,
% 3.80/4.01      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.80/4.01         = (k1_relat_1 @ sk_C))),
% 3.80/4.01      inference('sup-', [status(thm)], ['17', '18'])).
% 3.80/4.01  thf('20', plain,
% 3.80/4.01      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.80/4.01        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.80/4.01      inference('demod', [status(thm)], ['16', '19'])).
% 3.80/4.01  thf('21', plain,
% 3.80/4.01      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.80/4.01        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.80/4.01      inference('sup-', [status(thm)], ['13', '20'])).
% 3.80/4.01  thf(fc2_struct_0, axiom,
% 3.80/4.01    (![A:$i]:
% 3.80/4.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.80/4.01       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.80/4.01  thf('22', plain,
% 3.80/4.01      (![X29 : $i]:
% 3.80/4.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X29))
% 3.80/4.01          | ~ (l1_struct_0 @ X29)
% 3.80/4.01          | (v2_struct_0 @ X29))),
% 3.80/4.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.80/4.01  thf('23', plain,
% 3.80/4.01      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.80/4.01        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.80/4.01        | (v2_struct_0 @ sk_B)
% 3.80/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup-', [status(thm)], ['21', '22'])).
% 3.80/4.01  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.80/4.01  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.80/4.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.80/4.01  thf('25', plain, ((l1_struct_0 @ sk_B)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('26', plain,
% 3.80/4.01      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 3.80/4.01      inference('demod', [status(thm)], ['23', '24', '25'])).
% 3.80/4.01  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('28', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.01      inference('clc', [status(thm)], ['26', '27'])).
% 3.80/4.01  thf('29', plain,
% 3.80/4.01      ((m1_subset_1 @ sk_C @ 
% 3.80/4.01        (k1_zfmisc_1 @ 
% 3.80/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf(redefinition_k2_relset_1, axiom,
% 3.80/4.01    (![A:$i,B:$i,C:$i]:
% 3.80/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.80/4.01       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.80/4.01  thf('30', plain,
% 3.80/4.01      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.80/4.01         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 3.80/4.01          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.80/4.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.80/4.01  thf('31', plain,
% 3.80/4.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.80/4.01         = (k2_relat_1 @ sk_C))),
% 3.80/4.01      inference('sup-', [status(thm)], ['29', '30'])).
% 3.80/4.01  thf('32', plain,
% 3.80/4.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.80/4.01         = (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup+', [status(thm)], ['31', '32'])).
% 3.80/4.01  thf('34', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.01      inference('clc', [status(thm)], ['26', '27'])).
% 3.80/4.01  thf('35', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.01      inference('clc', [status(thm)], ['26', '27'])).
% 3.80/4.01  thf('36', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup+', [status(thm)], ['31', '32'])).
% 3.80/4.01  thf('37', plain,
% 3.80/4.01      (![X28 : $i]:
% 3.80/4.01         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 3.80/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.01  thf('38', plain,
% 3.80/4.01      ((m1_subset_1 @ sk_C @ 
% 3.80/4.01        (k1_zfmisc_1 @ 
% 3.80/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('39', plain,
% 3.80/4.01      (((m1_subset_1 @ sk_C @ 
% 3.80/4.01         (k1_zfmisc_1 @ 
% 3.80/4.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.80/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup+', [status(thm)], ['37', '38'])).
% 3.80/4.01  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('41', plain,
% 3.80/4.01      ((m1_subset_1 @ sk_C @ 
% 3.80/4.01        (k1_zfmisc_1 @ 
% 3.80/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.80/4.01      inference('demod', [status(thm)], ['39', '40'])).
% 3.80/4.01  thf('42', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup+', [status(thm)], ['31', '32'])).
% 3.80/4.01  thf('43', plain,
% 3.80/4.01      ((m1_subset_1 @ sk_C @ 
% 3.80/4.01        (k1_zfmisc_1 @ 
% 3.80/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 3.80/4.01      inference('demod', [status(thm)], ['41', '42'])).
% 3.80/4.01  thf('44', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.01      inference('clc', [status(thm)], ['26', '27'])).
% 3.80/4.01  thf('45', plain,
% 3.80/4.01      ((m1_subset_1 @ sk_C @ 
% 3.80/4.01        (k1_zfmisc_1 @ 
% 3.80/4.01         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 3.80/4.01      inference('demod', [status(thm)], ['43', '44'])).
% 3.80/4.01  thf(d4_tops_2, axiom,
% 3.80/4.01    (![A:$i,B:$i,C:$i]:
% 3.80/4.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.80/4.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/4.01       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.80/4.01         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 3.80/4.01  thf('46', plain,
% 3.80/4.01      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.80/4.01         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 3.80/4.01          | ~ (v2_funct_1 @ X32)
% 3.80/4.01          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 3.80/4.01          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 3.80/4.01          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 3.80/4.01          | ~ (v1_funct_1 @ X32))),
% 3.80/4.01      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.80/4.01  thf('47', plain,
% 3.80/4.01      ((~ (v1_funct_1 @ sk_C)
% 3.80/4.01        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 3.80/4.01        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.01            = (k2_funct_1 @ sk_C))
% 3.80/4.01        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.01        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.01            != (k2_relat_1 @ sk_C)))),
% 3.80/4.01      inference('sup-', [status(thm)], ['45', '46'])).
% 3.80/4.01  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('49', plain,
% 3.80/4.01      (![X28 : $i]:
% 3.80/4.01         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 3.80/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.01  thf('50', plain,
% 3.80/4.01      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('51', plain,
% 3.80/4.01      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.80/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup+', [status(thm)], ['49', '50'])).
% 3.80/4.01  thf('52', plain, ((l1_struct_0 @ sk_B)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('53', plain,
% 3.80/4.01      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('demod', [status(thm)], ['51', '52'])).
% 3.80/4.01  thf('54', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup+', [status(thm)], ['31', '32'])).
% 3.80/4.01  thf('55', plain,
% 3.80/4.01      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 3.80/4.01      inference('demod', [status(thm)], ['53', '54'])).
% 3.80/4.01  thf('56', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.01      inference('clc', [status(thm)], ['26', '27'])).
% 3.80/4.01  thf('57', plain,
% 3.80/4.01      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 3.80/4.01      inference('demod', [status(thm)], ['55', '56'])).
% 3.80/4.01  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('59', plain,
% 3.80/4.01      (![X28 : $i]:
% 3.80/4.01         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 3.80/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.01  thf('60', plain,
% 3.80/4.01      (![X28 : $i]:
% 3.80/4.01         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 3.80/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.01  thf('61', plain,
% 3.80/4.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.80/4.01         = (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('62', plain,
% 3.80/4.01      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.80/4.01          = (k2_struct_0 @ sk_B))
% 3.80/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup+', [status(thm)], ['60', '61'])).
% 3.80/4.01  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('64', plain,
% 3.80/4.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.80/4.01         = (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('demod', [status(thm)], ['62', '63'])).
% 3.80/4.01  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup+', [status(thm)], ['31', '32'])).
% 3.80/4.01  thf('66', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.80/4.01      inference('sup+', [status(thm)], ['31', '32'])).
% 3.80/4.01  thf('67', plain,
% 3.80/4.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.01         = (k2_relat_1 @ sk_C))),
% 3.80/4.01      inference('demod', [status(thm)], ['64', '65', '66'])).
% 3.80/4.01  thf('68', plain,
% 3.80/4.01      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.01          = (k2_relat_1 @ sk_C))
% 3.80/4.01        | ~ (l1_struct_0 @ sk_A))),
% 3.80/4.01      inference('sup+', [status(thm)], ['59', '67'])).
% 3.80/4.01  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('70', plain,
% 3.80/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.01         = (k2_relat_1 @ sk_C))),
% 3.80/4.01      inference('demod', [status(thm)], ['68', '69'])).
% 3.80/4.01  thf('71', plain,
% 3.80/4.01      (![X28 : $i]:
% 3.80/4.01         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 3.80/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.01  thf('72', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.01      inference('clc', [status(thm)], ['26', '27'])).
% 3.80/4.01  thf('73', plain,
% 3.80/4.01      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 3.80/4.01      inference('sup+', [status(thm)], ['71', '72'])).
% 3.80/4.01  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 3.80/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.01  thf('75', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.01      inference('demod', [status(thm)], ['73', '74'])).
% 3.80/4.01  thf('76', plain,
% 3.80/4.01      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.01         = (k2_relat_1 @ sk_C))),
% 3.80/4.01      inference('demod', [status(thm)], ['70', '75'])).
% 3.80/4.01  thf('77', plain,
% 3.80/4.01      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.02          = (k2_funct_1 @ sk_C))
% 3.80/4.02        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['47', '48', '57', '58', '76'])).
% 3.80/4.02  thf('78', plain,
% 3.80/4.02      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.02         = (k2_funct_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['77'])).
% 3.80/4.02  thf('79', plain,
% 3.80/4.02      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02           (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02          sk_C)),
% 3.80/4.02      inference('demod', [status(thm)],
% 3.80/4.02                ['8', '28', '33', '34', '35', '36', '78'])).
% 3.80/4.02  thf(fc6_funct_1, axiom,
% 3.80/4.02    (![A:$i]:
% 3.80/4.02     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 3.80/4.02       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.80/4.02         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 3.80/4.02         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.80/4.02  thf('80', plain,
% 3.80/4.02      (![X4 : $i]:
% 3.80/4.02         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.80/4.02          | ~ (v2_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_relat_1 @ X4))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.80/4.02  thf('81', plain,
% 3.80/4.02      ((m1_subset_1 @ sk_C @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 3.80/4.02      inference('demod', [status(thm)], ['43', '44'])).
% 3.80/4.02  thf(t31_funct_2, axiom,
% 3.80/4.02    (![A:$i,B:$i,C:$i]:
% 3.80/4.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.80/4.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/4.02       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.80/4.02         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.80/4.02           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.80/4.02           ( m1_subset_1 @
% 3.80/4.02             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.80/4.02  thf('82', plain,
% 3.80/4.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X25)
% 3.80/4.02          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 3.80/4.02          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 3.80/4.02             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.80/4.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 3.80/4.02          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 3.80/4.02          | ~ (v1_funct_1 @ X25))),
% 3.80/4.02      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.80/4.02  thf('83', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 3.80/4.02        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02           (k1_zfmisc_1 @ 
% 3.80/4.02            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 3.80/4.02        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.02            != (k2_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C))),
% 3.80/4.02      inference('sup-', [status(thm)], ['81', '82'])).
% 3.80/4.02  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('85', plain,
% 3.80/4.02      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['55', '56'])).
% 3.80/4.02  thf('86', plain,
% 3.80/4.02      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.02         = (k2_relat_1 @ sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['70', '75'])).
% 3.80/4.02  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('88', plain,
% 3.80/4.02      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02         (k1_zfmisc_1 @ 
% 3.80/4.02          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 3.80/4.02        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 3.80/4.02  thf('89', plain,
% 3.80/4.02      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 3.80/4.02      inference('simplify', [status(thm)], ['88'])).
% 3.80/4.02  thf('90', plain,
% 3.80/4.02      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.80/4.02         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 3.80/4.02          | ~ (v2_funct_1 @ X32)
% 3.80/4.02          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 3.80/4.02          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 3.80/4.02          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 3.80/4.02          | ~ (v1_funct_1 @ X32))),
% 3.80/4.02      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.80/4.02  thf('91', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 3.80/4.02             (k1_relat_1 @ sk_C))
% 3.80/4.02        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['89', '90'])).
% 3.80/4.02  thf('92', plain,
% 3.80/4.02      ((m1_subset_1 @ sk_C @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 3.80/4.02      inference('demod', [status(thm)], ['43', '44'])).
% 3.80/4.02  thf('93', plain,
% 3.80/4.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X25)
% 3.80/4.02          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 3.80/4.02          | (v1_funct_1 @ (k2_funct_1 @ X25))
% 3.80/4.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 3.80/4.02          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 3.80/4.02          | ~ (v1_funct_1 @ X25))),
% 3.80/4.02      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.80/4.02  thf('94', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.02            != (k2_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C))),
% 3.80/4.02      inference('sup-', [status(thm)], ['92', '93'])).
% 3.80/4.02  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('96', plain,
% 3.80/4.02      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['55', '56'])).
% 3.80/4.02  thf('97', plain,
% 3.80/4.02      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.02         = (k2_relat_1 @ sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['70', '75'])).
% 3.80/4.02  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('99', plain,
% 3.80/4.02      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 3.80/4.02  thf('100', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['99'])).
% 3.80/4.02  thf('101', plain,
% 3.80/4.02      ((m1_subset_1 @ sk_C @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 3.80/4.02      inference('demod', [status(thm)], ['43', '44'])).
% 3.80/4.02  thf('102', plain,
% 3.80/4.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X25)
% 3.80/4.02          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 3.80/4.02          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 3.80/4.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 3.80/4.02          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 3.80/4.02          | ~ (v1_funct_1 @ X25))),
% 3.80/4.02      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.80/4.02  thf('103', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 3.80/4.02           (k1_relat_1 @ sk_C))
% 3.80/4.02        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.02            != (k2_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C))),
% 3.80/4.02      inference('sup-', [status(thm)], ['101', '102'])).
% 3.80/4.02  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('105', plain,
% 3.80/4.02      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['55', '56'])).
% 3.80/4.02  thf('106', plain,
% 3.80/4.02      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.80/4.02         = (k2_relat_1 @ sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['70', '75'])).
% 3.80/4.02  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('108', plain,
% 3.80/4.02      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 3.80/4.02         (k1_relat_1 @ sk_C))
% 3.80/4.02        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 3.80/4.02  thf('109', plain,
% 3.80/4.02      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 3.80/4.02        (k1_relat_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['108'])).
% 3.80/4.02  thf('110', plain,
% 3.80/4.02      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 3.80/4.02      inference('simplify', [status(thm)], ['88'])).
% 3.80/4.02  thf('111', plain,
% 3.80/4.02      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.80/4.02         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 3.80/4.02          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.80/4.02      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.80/4.02  thf('112', plain,
% 3.80/4.02      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['110', '111'])).
% 3.80/4.02  thf('113', plain,
% 3.80/4.02      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['91', '100', '109', '112'])).
% 3.80/4.02  thf(t65_funct_1, axiom,
% 3.80/4.02    (![A:$i]:
% 3.80/4.02     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.80/4.02       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 3.80/4.02  thf('114', plain,
% 3.80/4.02      (![X6 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X6)
% 3.80/4.02          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 3.80/4.02          | ~ (v1_funct_1 @ X6)
% 3.80/4.02          | ~ (v1_relat_1 @ X6))),
% 3.80/4.02      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.80/4.02  thf(t55_funct_1, axiom,
% 3.80/4.02    (![A:$i]:
% 3.80/4.02     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.80/4.02       ( ( v2_funct_1 @ A ) =>
% 3.80/4.02         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.80/4.02           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.80/4.02  thf('115', plain,
% 3.80/4.02      (![X5 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X5)
% 3.80/4.02          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 3.80/4.02          | ~ (v1_funct_1 @ X5)
% 3.80/4.02          | ~ (v1_relat_1 @ X5))),
% 3.80/4.02      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.80/4.02  thf('116', plain,
% 3.80/4.02      (![X4 : $i]:
% 3.80/4.02         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.80/4.02          | ~ (v2_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_relat_1 @ X4))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.80/4.02  thf('117', plain,
% 3.80/4.02      (![X28 : $i]:
% 3.80/4.02         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 3.80/4.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.02  thf('118', plain,
% 3.80/4.02      ((m1_subset_1 @ sk_C @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('119', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.02      inference('clc', [status(thm)], ['26', '27'])).
% 3.80/4.02  thf('120', plain,
% 3.80/4.02      ((m1_subset_1 @ sk_C @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.02      inference('demod', [status(thm)], ['118', '119'])).
% 3.80/4.02  thf('121', plain,
% 3.80/4.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X25)
% 3.80/4.02          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 3.80/4.02          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 3.80/4.02             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.80/4.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 3.80/4.02          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 3.80/4.02          | ~ (v1_funct_1 @ X25))),
% 3.80/4.02      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.80/4.02  thf('122', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.80/4.02        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02           (k1_zfmisc_1 @ 
% 3.80/4.02            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 3.80/4.02        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.80/4.02            != (u1_struct_0 @ sk_B))
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C))),
% 3.80/4.02      inference('sup-', [status(thm)], ['120', '121'])).
% 3.80/4.02  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('124', plain,
% 3.80/4.02      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('125', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.02      inference('clc', [status(thm)], ['26', '27'])).
% 3.80/4.02  thf('126', plain,
% 3.80/4.02      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.80/4.02      inference('demod', [status(thm)], ['124', '125'])).
% 3.80/4.02  thf('127', plain,
% 3.80/4.02      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.80/4.02         = (k2_relat_1 @ sk_C))),
% 3.80/4.02      inference('sup-', [status(thm)], ['29', '30'])).
% 3.80/4.02  thf('128', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.80/4.02      inference('clc', [status(thm)], ['26', '27'])).
% 3.80/4.02  thf('129', plain,
% 3.80/4.02      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.80/4.02         = (k2_relat_1 @ sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['127', '128'])).
% 3.80/4.02  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('131', plain,
% 3.80/4.02      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02         (k1_zfmisc_1 @ 
% 3.80/4.02          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 3.80/4.02        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 3.80/4.02      inference('demod', [status(thm)], ['122', '123', '126', '129', '130'])).
% 3.80/4.02  thf('132', plain,
% 3.80/4.02      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 3.80/4.02        | ~ (l1_struct_0 @ sk_B)
% 3.80/4.02        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02           (k1_zfmisc_1 @ 
% 3.80/4.02            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 3.80/4.02      inference('sup-', [status(thm)], ['117', '131'])).
% 3.80/4.02  thf('133', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.80/4.02      inference('sup+', [status(thm)], ['31', '32'])).
% 3.80/4.02  thf('134', plain, ((l1_struct_0 @ sk_B)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('135', plain,
% 3.80/4.02      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 3.80/4.02        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02           (k1_zfmisc_1 @ 
% 3.80/4.02            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 3.80/4.02      inference('demod', [status(thm)], ['132', '133', '134'])).
% 3.80/4.02  thf('136', plain,
% 3.80/4.02      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.80/4.02      inference('simplify', [status(thm)], ['135'])).
% 3.80/4.02  thf('137', plain,
% 3.80/4.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X25)
% 3.80/4.02          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 3.80/4.02          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 3.80/4.02             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.80/4.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 3.80/4.02          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 3.80/4.02          | ~ (v1_funct_1 @ X25))),
% 3.80/4.02      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.80/4.02  thf('138', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02             (k1_relat_1 @ sk_C))
% 3.80/4.02        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_zfmisc_1 @ 
% 3.80/4.02            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 3.80/4.02        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['136', '137'])).
% 3.80/4.02  thf('139', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['99'])).
% 3.80/4.02  thf('140', plain,
% 3.80/4.02      (![X28 : $i]:
% 3.80/4.02         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 3.80/4.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.80/4.02  thf('141', plain,
% 3.80/4.02      ((m1_subset_1 @ sk_C @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.02      inference('demod', [status(thm)], ['118', '119'])).
% 3.80/4.02  thf('142', plain,
% 3.80/4.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X25)
% 3.80/4.02          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 3.80/4.02          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 3.80/4.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 3.80/4.02          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 3.80/4.02          | ~ (v1_funct_1 @ X25))),
% 3.80/4.02      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.80/4.02  thf('143', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.80/4.02        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02           (k1_relat_1 @ sk_C))
% 3.80/4.02        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.80/4.02            != (u1_struct_0 @ sk_B))
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C))),
% 3.80/4.02      inference('sup-', [status(thm)], ['141', '142'])).
% 3.80/4.02  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('145', plain,
% 3.80/4.02      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.80/4.02      inference('demod', [status(thm)], ['124', '125'])).
% 3.80/4.02  thf('146', plain,
% 3.80/4.02      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.80/4.02         = (k2_relat_1 @ sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['127', '128'])).
% 3.80/4.02  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('148', plain,
% 3.80/4.02      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02         (k1_relat_1 @ sk_C))
% 3.80/4.02        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 3.80/4.02      inference('demod', [status(thm)], ['143', '144', '145', '146', '147'])).
% 3.80/4.02  thf('149', plain,
% 3.80/4.02      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 3.80/4.02        | ~ (l1_struct_0 @ sk_B)
% 3.80/4.02        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02           (k1_relat_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['140', '148'])).
% 3.80/4.02  thf('150', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.80/4.02      inference('sup+', [status(thm)], ['31', '32'])).
% 3.80/4.02  thf('151', plain, ((l1_struct_0 @ sk_B)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('152', plain,
% 3.80/4.02      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02           (k1_relat_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['149', '150', '151'])).
% 3.80/4.02  thf('153', plain,
% 3.80/4.02      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02        (k1_relat_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['152'])).
% 3.80/4.02  thf('154', plain,
% 3.80/4.02      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02         (k1_zfmisc_1 @ 
% 3.80/4.02          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 3.80/4.02        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['138', '139', '153'])).
% 3.80/4.02  thf('155', plain,
% 3.80/4.02      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.80/4.02      inference('simplify', [status(thm)], ['135'])).
% 3.80/4.02  thf('156', plain,
% 3.80/4.02      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.80/4.02         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 3.80/4.02          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.80/4.02      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.80/4.02  thf('157', plain,
% 3.80/4.02      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['155', '156'])).
% 3.80/4.02  thf('158', plain,
% 3.80/4.02      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02         (k1_zfmisc_1 @ 
% 3.80/4.02          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 3.80/4.02        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['154', '157'])).
% 3.80/4.02  thf('159', plain,
% 3.80/4.02      ((~ (v1_relat_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.02        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_zfmisc_1 @ 
% 3.80/4.02            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 3.80/4.02      inference('sup-', [status(thm)], ['116', '158'])).
% 3.80/4.02  thf('160', plain,
% 3.80/4.02      ((m1_subset_1 @ sk_C @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf(cc2_relat_1, axiom,
% 3.80/4.02    (![A:$i]:
% 3.80/4.02     ( ( v1_relat_1 @ A ) =>
% 3.80/4.02       ( ![B:$i]:
% 3.80/4.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.80/4.02  thf('161', plain,
% 3.80/4.02      (![X0 : $i, X1 : $i]:
% 3.80/4.02         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.80/4.02          | (v1_relat_1 @ X0)
% 3.80/4.02          | ~ (v1_relat_1 @ X1))),
% 3.80/4.02      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.80/4.02  thf('162', plain,
% 3.80/4.02      ((~ (v1_relat_1 @ 
% 3.80/4.02           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 3.80/4.02        | (v1_relat_1 @ sk_C))),
% 3.80/4.02      inference('sup-', [status(thm)], ['160', '161'])).
% 3.80/4.02  thf(fc6_relat_1, axiom,
% 3.80/4.02    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.80/4.02  thf('163', plain,
% 3.80/4.02      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.80/4.02  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['162', '163'])).
% 3.80/4.02  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('167', plain,
% 3.80/4.02      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_zfmisc_1 @ 
% 3.80/4.02            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 3.80/4.02      inference('demod', [status(thm)], ['159', '164', '165', '166'])).
% 3.80/4.02  thf('168', plain,
% 3.80/4.02      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v1_relat_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.02        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_zfmisc_1 @ 
% 3.80/4.02            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 3.80/4.02      inference('sup-', [status(thm)], ['115', '167'])).
% 3.80/4.02  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['162', '163'])).
% 3.80/4.02  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('172', plain,
% 3.80/4.02      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_zfmisc_1 @ 
% 3.80/4.02            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 3.80/4.02      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 3.80/4.02  thf('173', plain,
% 3.80/4.02      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.02      inference('simplify', [status(thm)], ['172'])).
% 3.80/4.02  thf('174', plain,
% 3.80/4.02      ((m1_subset_1 @ sk_C @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.02      inference('demod', [status(thm)], ['118', '119'])).
% 3.80/4.02  thf(redefinition_r2_funct_2, axiom,
% 3.80/4.02    (![A:$i,B:$i,C:$i,D:$i]:
% 3.80/4.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.80/4.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.80/4.02         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.80/4.02         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.80/4.02       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.80/4.02  thf('175', plain,
% 3.80/4.02      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.80/4.02         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.80/4.02          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 3.80/4.02          | ~ (v1_funct_1 @ X21)
% 3.80/4.02          | ~ (v1_funct_1 @ X24)
% 3.80/4.02          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 3.80/4.02          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.80/4.02          | ((X21) = (X24))
% 3.80/4.02          | ~ (r2_funct_2 @ X22 @ X23 @ X21 @ X24))),
% 3.80/4.02      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 3.80/4.02  thf('176', plain,
% 3.80/4.02      (![X0 : $i]:
% 3.80/4.02         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.80/4.02             X0)
% 3.80/4.02          | ((sk_C) = (X0))
% 3.80/4.02          | ~ (m1_subset_1 @ X0 @ 
% 3.80/4.02               (k1_zfmisc_1 @ 
% 3.80/4.02                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 3.80/4.02          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['174', '175'])).
% 3.80/4.02  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('178', plain,
% 3.80/4.02      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.80/4.02      inference('demod', [status(thm)], ['124', '125'])).
% 3.80/4.02  thf('179', plain,
% 3.80/4.02      (![X0 : $i]:
% 3.80/4.02         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.80/4.02             X0)
% 3.80/4.02          | ((sk_C) = (X0))
% 3.80/4.02          | ~ (m1_subset_1 @ X0 @ 
% 3.80/4.02               (k1_zfmisc_1 @ 
% 3.80/4.02                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 3.80/4.02          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.80/4.02          | ~ (v1_funct_1 @ X0))),
% 3.80/4.02      inference('demod', [status(thm)], ['176', '177', '178'])).
% 3.80/4.02  thf('180', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02             (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.80/4.02        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.80/4.02             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.02      inference('sup-', [status(thm)], ['173', '179'])).
% 3.80/4.02  thf('181', plain,
% 3.80/4.02      (![X5 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X5)
% 3.80/4.02          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 3.80/4.02          | ~ (v1_funct_1 @ X5)
% 3.80/4.02          | ~ (v1_relat_1 @ X5))),
% 3.80/4.02      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.80/4.02  thf('182', plain,
% 3.80/4.02      (![X4 : $i]:
% 3.80/4.02         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.80/4.02          | ~ (v2_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_relat_1 @ X4))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.80/4.02  thf('183', plain,
% 3.80/4.02      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.80/4.02      inference('simplify', [status(thm)], ['135'])).
% 3.80/4.02  thf('184', plain,
% 3.80/4.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X25)
% 3.80/4.02          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 3.80/4.02          | (v1_funct_1 @ (k2_funct_1 @ X25))
% 3.80/4.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 3.80/4.02          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 3.80/4.02          | ~ (v1_funct_1 @ X25))),
% 3.80/4.02      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.80/4.02  thf('185', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02             (k1_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['183', '184'])).
% 3.80/4.02  thf('186', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['99'])).
% 3.80/4.02  thf('187', plain,
% 3.80/4.02      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02        (k1_relat_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['152'])).
% 3.80/4.02  thf('188', plain,
% 3.80/4.02      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['185', '186', '187'])).
% 3.80/4.02  thf('189', plain,
% 3.80/4.02      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['155', '156'])).
% 3.80/4.02  thf('190', plain,
% 3.80/4.02      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['188', '189'])).
% 3.80/4.02  thf('191', plain,
% 3.80/4.02      ((~ (v1_relat_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.02        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.02      inference('sup-', [status(thm)], ['182', '190'])).
% 3.80/4.02  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['162', '163'])).
% 3.80/4.02  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('195', plain,
% 3.80/4.02      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.02      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 3.80/4.02  thf('196', plain,
% 3.80/4.02      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v1_relat_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.02        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.02      inference('sup-', [status(thm)], ['181', '195'])).
% 3.80/4.02  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['162', '163'])).
% 3.80/4.02  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('199', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('200', plain,
% 3.80/4.02      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.02      inference('demod', [status(thm)], ['196', '197', '198', '199'])).
% 3.80/4.02  thf('201', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('simplify', [status(thm)], ['200'])).
% 3.80/4.02  thf('202', plain,
% 3.80/4.02      (![X5 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X5)
% 3.80/4.02          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 3.80/4.02          | ~ (v1_funct_1 @ X5)
% 3.80/4.02          | ~ (v1_relat_1 @ X5))),
% 3.80/4.02      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.80/4.02  thf('203', plain,
% 3.80/4.02      (![X4 : $i]:
% 3.80/4.02         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.80/4.02          | ~ (v2_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_relat_1 @ X4))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.80/4.02  thf('204', plain,
% 3.80/4.02      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.80/4.02      inference('simplify', [status(thm)], ['135'])).
% 3.80/4.02  thf('205', plain,
% 3.80/4.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X25)
% 3.80/4.02          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 3.80/4.02          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 3.80/4.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 3.80/4.02          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 3.80/4.02          | ~ (v1_funct_1 @ X25))),
% 3.80/4.02      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.80/4.02  thf('206', plain,
% 3.80/4.02      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02             (k1_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.80/4.02        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['204', '205'])).
% 3.80/4.02  thf('207', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['99'])).
% 3.80/4.02  thf('208', plain,
% 3.80/4.02      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.80/4.02        (k1_relat_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['152'])).
% 3.80/4.02  thf('209', plain,
% 3.80/4.02      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.80/4.02        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['206', '207', '208'])).
% 3.80/4.02  thf('210', plain,
% 3.80/4.02      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['155', '156'])).
% 3.80/4.02  thf('211', plain,
% 3.80/4.02      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.80/4.02        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['209', '210'])).
% 3.80/4.02  thf('212', plain,
% 3.80/4.02      ((~ (v1_relat_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.02        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['203', '211'])).
% 3.80/4.02  thf('213', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['162', '163'])).
% 3.80/4.02  thf('214', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('215', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('216', plain,
% 3.80/4.02      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.80/4.02      inference('demod', [status(thm)], ['212', '213', '214', '215'])).
% 3.80/4.02  thf('217', plain,
% 3.80/4.02      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | ~ (v1_relat_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.02        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['202', '216'])).
% 3.80/4.02  thf('218', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['162', '163'])).
% 3.80/4.02  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('220', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('221', plain,
% 3.80/4.02      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.80/4.02        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.80/4.02      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 3.80/4.02  thf('222', plain,
% 3.80/4.02      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.80/4.02        (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.80/4.02      inference('simplify', [status(thm)], ['221'])).
% 3.80/4.02  thf('223', plain,
% 3.80/4.02      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.80/4.02             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.02      inference('demod', [status(thm)], ['180', '201', '222'])).
% 3.80/4.02  thf('224', plain,
% 3.80/4.02      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.80/4.02           sk_C)
% 3.80/4.02        | ~ (v1_relat_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.02        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.02      inference('sup-', [status(thm)], ['114', '223'])).
% 3.80/4.02  thf('225', plain,
% 3.80/4.02      ((m1_subset_1 @ sk_C @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.80/4.02      inference('demod', [status(thm)], ['118', '119'])).
% 3.80/4.02  thf('226', plain,
% 3.80/4.02      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.80/4.02         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.80/4.02          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 3.80/4.02          | ~ (v1_funct_1 @ X21)
% 3.80/4.02          | ~ (v1_funct_1 @ X24)
% 3.80/4.02          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 3.80/4.02          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.80/4.02          | (r2_funct_2 @ X22 @ X23 @ X21 @ X24)
% 3.80/4.02          | ((X21) != (X24)))),
% 3.80/4.02      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 3.80/4.02  thf('227', plain,
% 3.80/4.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.80/4.02         ((r2_funct_2 @ X22 @ X23 @ X24 @ X24)
% 3.80/4.02          | ~ (v1_funct_1 @ X24)
% 3.80/4.02          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 3.80/4.02          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.80/4.02      inference('simplify', [status(thm)], ['226'])).
% 3.80/4.02  thf('228', plain,
% 3.80/4.02      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.80/4.02           sk_C))),
% 3.80/4.02      inference('sup-', [status(thm)], ['225', '227'])).
% 3.80/4.02  thf('229', plain,
% 3.80/4.02      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.80/4.02      inference('demod', [status(thm)], ['124', '125'])).
% 3.80/4.02  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('231', plain,
% 3.80/4.02      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['228', '229', '230'])).
% 3.80/4.02  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['162', '163'])).
% 3.80/4.02  thf('233', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('234', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('235', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['224', '231', '232', '233', '234'])).
% 3.80/4.02  thf('236', plain,
% 3.80/4.02      (![X4 : $i]:
% 3.80/4.02         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.80/4.02          | ~ (v2_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_relat_1 @ X4))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.80/4.02  thf('237', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['224', '231', '232', '233', '234'])).
% 3.80/4.02  thf('238', plain,
% 3.80/4.02      (![X4 : $i]:
% 3.80/4.02         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 3.80/4.02          | ~ (v2_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_relat_1 @ X4))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.80/4.02  thf('239', plain,
% 3.80/4.02      (![X4 : $i]:
% 3.80/4.02         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 3.80/4.02          | ~ (v2_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_relat_1 @ X4))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.80/4.02  thf('240', plain,
% 3.80/4.02      (![X4 : $i]:
% 3.80/4.02         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 3.80/4.02          | ~ (v2_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_funct_1 @ X4)
% 3.80/4.02          | ~ (v1_relat_1 @ X4))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.80/4.02  thf('241', plain,
% 3.80/4.02      (![X6 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X6)
% 3.80/4.02          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 3.80/4.02          | ~ (v1_funct_1 @ X6)
% 3.80/4.02          | ~ (v1_relat_1 @ X6))),
% 3.80/4.02      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.80/4.02  thf('242', plain,
% 3.80/4.02      (![X5 : $i]:
% 3.80/4.02         (~ (v2_funct_1 @ X5)
% 3.80/4.02          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 3.80/4.02          | ~ (v1_funct_1 @ X5)
% 3.80/4.02          | ~ (v1_relat_1 @ X5))),
% 3.80/4.02      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.80/4.02  thf('243', plain,
% 3.80/4.02      (![X0 : $i]:
% 3.80/4.02         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 3.80/4.02          | ~ (v1_relat_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.80/4.02          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.80/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.80/4.02      inference('sup+', [status(thm)], ['241', '242'])).
% 3.80/4.02  thf('244', plain,
% 3.80/4.02      (![X0 : $i]:
% 3.80/4.02         (~ (v1_relat_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.80/4.02          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_relat_1 @ X0)
% 3.80/4.02          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['240', '243'])).
% 3.80/4.02  thf('245', plain,
% 3.80/4.02      (![X0 : $i]:
% 3.80/4.02         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 3.80/4.02          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.80/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_relat_1 @ X0))),
% 3.80/4.02      inference('simplify', [status(thm)], ['244'])).
% 3.80/4.02  thf('246', plain,
% 3.80/4.02      (![X0 : $i]:
% 3.80/4.02         (~ (v1_relat_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_relat_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.80/4.02          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['239', '245'])).
% 3.80/4.02  thf('247', plain,
% 3.80/4.02      (![X0 : $i]:
% 3.80/4.02         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 3.80/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_relat_1 @ X0))),
% 3.80/4.02      inference('simplify', [status(thm)], ['246'])).
% 3.80/4.02  thf('248', plain,
% 3.80/4.02      (![X0 : $i]:
% 3.80/4.02         (~ (v1_relat_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_relat_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['238', '247'])).
% 3.80/4.02  thf('249', plain,
% 3.80/4.02      (![X0 : $i]:
% 3.80/4.02         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 3.80/4.02          | ~ (v2_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_funct_1 @ X0)
% 3.80/4.02          | ~ (v1_relat_1 @ X0))),
% 3.80/4.02      inference('simplify', [status(thm)], ['248'])).
% 3.80/4.02  thf('250', plain,
% 3.80/4.02      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('sup+', [status(thm)], ['237', '249'])).
% 3.80/4.02  thf('251', plain,
% 3.80/4.02      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.80/4.02        (k1_zfmisc_1 @ 
% 3.80/4.02         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 3.80/4.02      inference('simplify', [status(thm)], ['88'])).
% 3.80/4.02  thf('252', plain,
% 3.80/4.02      (![X0 : $i, X1 : $i]:
% 3.80/4.02         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.80/4.02          | (v1_relat_1 @ X0)
% 3.80/4.02          | ~ (v1_relat_1 @ X1))),
% 3.80/4.02      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.80/4.02  thf('253', plain,
% 3.80/4.02      ((~ (v1_relat_1 @ 
% 3.80/4.02           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 3.80/4.02        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['251', '252'])).
% 3.80/4.02  thf('254', plain,
% 3.80/4.02      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.80/4.02      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.80/4.02  thf('255', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['253', '254'])).
% 3.80/4.02  thf('256', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.80/4.02      inference('simplify', [status(thm)], ['99'])).
% 3.80/4.02  thf('257', plain,
% 3.80/4.02      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['250', '255', '256'])).
% 3.80/4.02  thf('258', plain,
% 3.80/4.02      ((~ (v1_relat_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.02        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.80/4.02      inference('sup-', [status(thm)], ['236', '257'])).
% 3.80/4.02  thf('259', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['162', '163'])).
% 3.80/4.02  thf('260', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('261', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('262', plain,
% 3.80/4.02      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['258', '259', '260', '261'])).
% 3.80/4.02  thf('263', plain,
% 3.80/4.02      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02          (k2_funct_1 @ sk_C)) = (sk_C))
% 3.80/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 3.80/4.02      inference('demod', [status(thm)], ['113', '235', '262'])).
% 3.80/4.02  thf('264', plain,
% 3.80/4.02      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.80/4.02        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 3.80/4.02      inference('simplify', [status(thm)], ['263'])).
% 3.80/4.02  thf('265', plain,
% 3.80/4.02      ((~ (v1_relat_1 @ sk_C)
% 3.80/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.80/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.80/4.02        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 3.80/4.02      inference('sup-', [status(thm)], ['80', '264'])).
% 3.80/4.02  thf('266', plain, ((v1_relat_1 @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['162', '163'])).
% 3.80/4.02  thf('267', plain, ((v1_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('268', plain, ((v2_funct_1 @ sk_C)),
% 3.80/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.02  thf('269', plain,
% 3.80/4.02      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 3.80/4.02         (k2_funct_1 @ sk_C)) = (sk_C))),
% 3.80/4.02      inference('demod', [status(thm)], ['265', '266', '267', '268'])).
% 3.80/4.02  thf('270', plain,
% 3.80/4.02      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 3.80/4.02      inference('demod', [status(thm)], ['228', '229', '230'])).
% 3.80/4.02  thf('271', plain, ($false),
% 3.80/4.02      inference('demod', [status(thm)], ['79', '269', '270'])).
% 3.80/4.02  
% 3.80/4.02  % SZS output end Refutation
% 3.80/4.02  
% 3.80/4.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
