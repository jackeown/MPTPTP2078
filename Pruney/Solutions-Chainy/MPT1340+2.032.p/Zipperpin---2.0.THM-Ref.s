%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AdScU9FgQg

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:11 EST 2020

% Result     : Theorem 4.67s
% Output     : Refutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :  302 (6274 expanded)
%              Number of leaves         :   44 (1875 expanded)
%              Depth                    :   35
%              Number of atoms          : 2904 (136510 expanded)
%              Number of equality atoms :  161 (4869 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X29 @ X31 )
       != X29 )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_tops_2 @ X30 @ X29 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
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
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('66',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('69',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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

thf(t62_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X29 @ X31 )
       != X29 )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_tops_2 @ X30 @ X29 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('116',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('117',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
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
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('142',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('161',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['159','162','163','164'])).

thf('166',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['115','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
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

thf('173',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_funct_2 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['171','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('180',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('181',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('182',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('183',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('185',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('186',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('188',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['180','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['179','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('201',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('202',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('203',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('204',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('206',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('207',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('209',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['201','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('212',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['210','211','212','213'])).

thf('215',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['200','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['215','216','217','218'])).

thf('220',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['178','199','220'])).

thf('222',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['114','221'])).

thf('223',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('224',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_funct_2 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('225',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_funct_2 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['223','225'])).

thf('227',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('231',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['222','229','230','231','232'])).

thf('234',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf('235',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['222','229','230','231','232'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('237',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('238',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('239',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('240',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('242',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['237','240','241'])).

thf('243',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['234','242'])).

thf('244',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('245',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['243','244','245','246'])).

thf('248',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['113','233','247'])).

thf('249',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['80','249'])).

thf('251',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['160','161'])).

thf('252',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['250','251','252','253'])).

thf('255',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('256',plain,(
    $false ),
    inference(demod,[status(thm)],['79','254','255'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AdScU9FgQg
% 0.13/0.38  % Computer   : n019.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 10:59:38 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.39  % Python version: Python 3.6.8
% 0.13/0.39  % Running in FO mode
% 4.67/4.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.67/4.90  % Solved by: fo/fo7.sh
% 4.67/4.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.67/4.90  % done 1105 iterations in 4.405s
% 4.67/4.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.67/4.90  % SZS output start Refutation
% 4.67/4.90  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.67/4.90  thf(sk_C_type, type, sk_C: $i).
% 4.67/4.90  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.67/4.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.67/4.90  thf(sk_B_type, type, sk_B: $i).
% 4.67/4.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.67/4.90  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.67/4.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.67/4.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.67/4.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.67/4.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.67/4.90  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 4.67/4.90  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.67/4.90  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.67/4.90  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.67/4.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.67/4.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.67/4.90  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 4.67/4.90  thf(sk_A_type, type, sk_A: $i).
% 4.67/4.90  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.67/4.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.67/4.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.67/4.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.67/4.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.67/4.90  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.67/4.90  thf(d3_struct_0, axiom,
% 4.67/4.90    (![A:$i]:
% 4.67/4.90     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.67/4.90  thf('0', plain,
% 4.67/4.90      (![X27 : $i]:
% 4.67/4.90         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.67/4.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.67/4.90  thf('1', plain,
% 4.67/4.90      (![X27 : $i]:
% 4.67/4.90         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.67/4.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.67/4.90  thf(t64_tops_2, conjecture,
% 4.67/4.90    (![A:$i]:
% 4.67/4.90     ( ( l1_struct_0 @ A ) =>
% 4.67/4.90       ( ![B:$i]:
% 4.67/4.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 4.67/4.90           ( ![C:$i]:
% 4.67/4.90             ( ( ( v1_funct_1 @ C ) & 
% 4.67/4.90                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.67/4.90                 ( m1_subset_1 @
% 4.67/4.90                   C @ 
% 4.67/4.90                   ( k1_zfmisc_1 @
% 4.67/4.90                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.67/4.90               ( ( ( ( k2_relset_1 @
% 4.67/4.90                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.67/4.90                     ( k2_struct_0 @ B ) ) & 
% 4.67/4.90                   ( v2_funct_1 @ C ) ) =>
% 4.67/4.90                 ( r2_funct_2 @
% 4.67/4.90                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 4.67/4.90                   ( k2_tops_2 @
% 4.67/4.90                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.67/4.90                     ( k2_tops_2 @
% 4.67/4.90                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 4.67/4.90                   C ) ) ) ) ) ) ))).
% 4.67/4.90  thf(zf_stmt_0, negated_conjecture,
% 4.67/4.90    (~( ![A:$i]:
% 4.67/4.90        ( ( l1_struct_0 @ A ) =>
% 4.67/4.90          ( ![B:$i]:
% 4.67/4.90            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 4.67/4.90              ( ![C:$i]:
% 4.67/4.90                ( ( ( v1_funct_1 @ C ) & 
% 4.67/4.90                    ( v1_funct_2 @
% 4.67/4.90                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.67/4.90                    ( m1_subset_1 @
% 4.67/4.90                      C @ 
% 4.67/4.90                      ( k1_zfmisc_1 @
% 4.67/4.90                        ( k2_zfmisc_1 @
% 4.67/4.90                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.67/4.90                  ( ( ( ( k2_relset_1 @
% 4.67/4.90                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.67/4.90                        ( k2_struct_0 @ B ) ) & 
% 4.67/4.90                      ( v2_funct_1 @ C ) ) =>
% 4.67/4.90                    ( r2_funct_2 @
% 4.67/4.90                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 4.67/4.90                      ( k2_tops_2 @
% 4.67/4.90                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.67/4.90                        ( k2_tops_2 @
% 4.67/4.90                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 4.67/4.90                      C ) ) ) ) ) ) ) )),
% 4.67/4.90    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 4.67/4.90  thf('2', plain,
% 4.67/4.90      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.90          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.67/4.90           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 4.67/4.90          sk_C)),
% 4.67/4.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.90  thf('3', plain,
% 4.67/4.90      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.90           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.67/4.90            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 4.67/4.90           sk_C)
% 4.67/4.90        | ~ (l1_struct_0 @ sk_B))),
% 4.67/4.90      inference('sup-', [status(thm)], ['1', '2'])).
% 4.67/4.90  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 4.67/4.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.90  thf('5', plain,
% 4.67/4.90      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.90          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.67/4.90           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 4.67/4.90          sk_C)),
% 4.67/4.90      inference('demod', [status(thm)], ['3', '4'])).
% 4.67/4.90  thf('6', plain,
% 4.67/4.90      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.90           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.67/4.90            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 4.67/4.90           sk_C)
% 4.67/4.90        | ~ (l1_struct_0 @ sk_B))),
% 4.67/4.90      inference('sup-', [status(thm)], ['0', '5'])).
% 4.67/4.90  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 4.67/4.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.90  thf('8', plain,
% 4.67/4.90      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.90          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.67/4.90           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 4.67/4.90          sk_C)),
% 4.67/4.90      inference('demod', [status(thm)], ['6', '7'])).
% 4.67/4.90  thf(d1_funct_2, axiom,
% 4.67/4.90    (![A:$i,B:$i,C:$i]:
% 4.67/4.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.67/4.90       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.67/4.90           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.67/4.90             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.67/4.90         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.67/4.90           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.67/4.90             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.67/4.90  thf(zf_stmt_1, axiom,
% 4.67/4.90    (![B:$i,A:$i]:
% 4.67/4.90     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.67/4.90       ( zip_tseitin_0 @ B @ A ) ))).
% 4.67/4.90  thf('9', plain,
% 4.67/4.90      (![X12 : $i, X13 : $i]:
% 4.67/4.90         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 4.67/4.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.67/4.90  thf('10', plain,
% 4.67/4.90      ((m1_subset_1 @ sk_C @ 
% 4.67/4.90        (k1_zfmisc_1 @ 
% 4.67/4.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.90  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.67/4.90  thf(zf_stmt_3, axiom,
% 4.67/4.90    (![C:$i,B:$i,A:$i]:
% 4.67/4.90     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.67/4.90       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.67/4.90  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.67/4.90  thf(zf_stmt_5, axiom,
% 4.67/4.90    (![A:$i,B:$i,C:$i]:
% 4.67/4.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.67/4.90       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.67/4.90         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.67/4.90           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.67/4.90             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.67/4.90  thf('11', plain,
% 4.67/4.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.67/4.90         (~ (zip_tseitin_0 @ X17 @ X18)
% 4.67/4.90          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 4.67/4.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 4.67/4.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.67/4.90  thf('12', plain,
% 4.67/4.90      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.67/4.90        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.67/4.90      inference('sup-', [status(thm)], ['10', '11'])).
% 4.67/4.90  thf('13', plain,
% 4.67/4.90      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 4.67/4.90        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.67/4.90      inference('sup-', [status(thm)], ['9', '12'])).
% 4.67/4.90  thf('14', plain,
% 4.67/4.90      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.67/4.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.90  thf('15', plain,
% 4.67/4.90      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.67/4.90         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 4.67/4.90          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 4.67/4.90          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 4.67/4.90      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.67/4.90  thf('16', plain,
% 4.67/4.90      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.67/4.90        | ((u1_struct_0 @ sk_A)
% 4.67/4.90            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 4.67/4.90      inference('sup-', [status(thm)], ['14', '15'])).
% 4.67/4.90  thf('17', plain,
% 4.67/4.90      ((m1_subset_1 @ sk_C @ 
% 4.67/4.90        (k1_zfmisc_1 @ 
% 4.67/4.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.90  thf(redefinition_k1_relset_1, axiom,
% 4.67/4.90    (![A:$i,B:$i,C:$i]:
% 4.67/4.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.67/4.90       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.67/4.90  thf('18', plain,
% 4.67/4.90      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.67/4.90         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 4.67/4.90          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 4.67/4.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.67/4.90  thf('19', plain,
% 4.67/4.90      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.67/4.90         = (k1_relat_1 @ sk_C))),
% 4.67/4.90      inference('sup-', [status(thm)], ['17', '18'])).
% 4.67/4.90  thf('20', plain,
% 4.67/4.90      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.67/4.90        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 4.67/4.90      inference('demod', [status(thm)], ['16', '19'])).
% 4.67/4.90  thf('21', plain,
% 4.67/4.90      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 4.67/4.90        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 4.67/4.90      inference('sup-', [status(thm)], ['13', '20'])).
% 4.67/4.90  thf(fc2_struct_0, axiom,
% 4.67/4.90    (![A:$i]:
% 4.67/4.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.67/4.90       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.67/4.90  thf('22', plain,
% 4.67/4.90      (![X28 : $i]:
% 4.67/4.90         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 4.67/4.91          | ~ (l1_struct_0 @ X28)
% 4.67/4.91          | (v2_struct_0 @ X28))),
% 4.67/4.91      inference('cnf', [status(esa)], [fc2_struct_0])).
% 4.67/4.91  thf('23', plain,
% 4.67/4.91      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.67/4.91        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 4.67/4.91        | (v2_struct_0 @ sk_B)
% 4.67/4.91        | ~ (l1_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup-', [status(thm)], ['21', '22'])).
% 4.67/4.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.67/4.91  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.67/4.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.67/4.91  thf('25', plain, ((l1_struct_0 @ sk_B)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('26', plain,
% 4.67/4.91      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 4.67/4.91      inference('demod', [status(thm)], ['23', '24', '25'])).
% 4.67/4.91  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('28', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('clc', [status(thm)], ['26', '27'])).
% 4.67/4.91  thf('29', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf(redefinition_k2_relset_1, axiom,
% 4.67/4.91    (![A:$i,B:$i,C:$i]:
% 4.67/4.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.67/4.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.67/4.91  thf('30', plain,
% 4.67/4.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.67/4.91         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 4.67/4.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.67/4.91  thf('31', plain,
% 4.67/4.91      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['29', '30'])).
% 4.67/4.91  thf('32', plain,
% 4.67/4.91      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.67/4.91         = (k2_struct_0 @ sk_B))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['31', '32'])).
% 4.67/4.91  thf('34', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('clc', [status(thm)], ['26', '27'])).
% 4.67/4.91  thf('35', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('clc', [status(thm)], ['26', '27'])).
% 4.67/4.91  thf('36', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['31', '32'])).
% 4.67/4.91  thf('37', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.67/4.91  thf('38', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('39', plain,
% 4.67/4.91      (((m1_subset_1 @ sk_C @ 
% 4.67/4.91         (k1_zfmisc_1 @ 
% 4.67/4.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 4.67/4.91        | ~ (l1_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['37', '38'])).
% 4.67/4.91  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('41', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 4.67/4.91      inference('demod', [status(thm)], ['39', '40'])).
% 4.67/4.91  thf('42', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['31', '32'])).
% 4.67/4.91  thf('43', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.67/4.91      inference('demod', [status(thm)], ['41', '42'])).
% 4.67/4.91  thf('44', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('clc', [status(thm)], ['26', '27'])).
% 4.67/4.91  thf('45', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.67/4.91      inference('demod', [status(thm)], ['43', '44'])).
% 4.67/4.91  thf(d4_tops_2, axiom,
% 4.67/4.91    (![A:$i,B:$i,C:$i]:
% 4.67/4.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.67/4.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.67/4.91       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 4.67/4.91         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 4.67/4.91  thf('46', plain,
% 4.67/4.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.67/4.91         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 4.67/4.91          | ~ (v2_funct_1 @ X31)
% 4.67/4.91          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 4.67/4.91          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 4.67/4.91          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 4.67/4.91          | ~ (v1_funct_1 @ X31))),
% 4.67/4.91      inference('cnf', [status(esa)], [d4_tops_2])).
% 4.67/4.91  thf('47', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.67/4.91        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91            = (k2_funct_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91            != (k2_relat_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['45', '46'])).
% 4.67/4.91  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('49', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.67/4.91  thf('50', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('51', plain,
% 4.67/4.91      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 4.67/4.91        | ~ (l1_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['49', '50'])).
% 4.67/4.91  thf('52', plain, ((l1_struct_0 @ sk_B)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('53', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 4.67/4.91      inference('demod', [status(thm)], ['51', '52'])).
% 4.67/4.91  thf('54', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['31', '32'])).
% 4.67/4.91  thf('55', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['53', '54'])).
% 4.67/4.91  thf('56', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('clc', [status(thm)], ['26', '27'])).
% 4.67/4.91  thf('57', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['55', '56'])).
% 4.67/4.91  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('59', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.67/4.91  thf('60', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.67/4.91  thf('61', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('62', plain,
% 4.67/4.91      (((m1_subset_1 @ sk_C @ 
% 4.67/4.91         (k1_zfmisc_1 @ 
% 4.67/4.91          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 4.67/4.91        | ~ (l1_struct_0 @ sk_A))),
% 4.67/4.91      inference('sup+', [status(thm)], ['60', '61'])).
% 4.67/4.91  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('64', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('demod', [status(thm)], ['62', '63'])).
% 4.67/4.91  thf('65', plain,
% 4.67/4.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.67/4.91         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 4.67/4.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.67/4.91  thf('66', plain,
% 4.67/4.91      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['64', '65'])).
% 4.67/4.91  thf('67', plain,
% 4.67/4.91      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 4.67/4.91          = (k2_relat_1 @ sk_C))
% 4.67/4.91        | ~ (l1_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['59', '66'])).
% 4.67/4.91  thf('68', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['31', '32'])).
% 4.67/4.91  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('70', plain,
% 4.67/4.91      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['67', '68', '69'])).
% 4.67/4.91  thf('71', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.67/4.91  thf('72', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('clc', [status(thm)], ['26', '27'])).
% 4.67/4.91  thf('73', plain,
% 4.67/4.91      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 4.67/4.91      inference('sup+', [status(thm)], ['71', '72'])).
% 4.67/4.91  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('75', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['73', '74'])).
% 4.67/4.91  thf('76', plain,
% 4.67/4.91      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['70', '75'])).
% 4.67/4.91  thf('77', plain,
% 4.67/4.91      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91          = (k2_funct_1 @ sk_C))
% 4.67/4.91        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['47', '48', '57', '58', '76'])).
% 4.67/4.91  thf('78', plain,
% 4.67/4.91      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91         = (k2_funct_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['77'])).
% 4.67/4.91  thf('79', plain,
% 4.67/4.91      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91           (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91          sk_C)),
% 4.67/4.91      inference('demod', [status(thm)],
% 4.67/4.91                ['8', '28', '33', '34', '35', '36', '78'])).
% 4.67/4.91  thf(t62_funct_1, axiom,
% 4.67/4.91    (![A:$i]:
% 4.67/4.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.67/4.91       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.67/4.91  thf('80', plain,
% 4.67/4.91      (![X1 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X1)
% 4.67/4.91          | (v2_funct_1 @ (k2_funct_1 @ X1))
% 4.67/4.91          | ~ (v1_funct_1 @ X1)
% 4.67/4.91          | ~ (v1_relat_1 @ X1))),
% 4.67/4.91      inference('cnf', [status(esa)], [t62_funct_1])).
% 4.67/4.91  thf('81', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.67/4.91      inference('demod', [status(thm)], ['43', '44'])).
% 4.67/4.91  thf(t31_funct_2, axiom,
% 4.67/4.91    (![A:$i,B:$i,C:$i]:
% 4.67/4.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.67/4.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.67/4.91       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.67/4.91         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.67/4.91           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.67/4.91           ( m1_subset_1 @
% 4.67/4.91             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 4.67/4.91  thf('82', plain,
% 4.67/4.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X24)
% 4.67/4.91          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.67/4.91          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 4.67/4.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.67/4.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.67/4.91          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.67/4.91          | ~ (v1_funct_1 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.67/4.91  thf('83', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.67/4.91        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91           (k1_zfmisc_1 @ 
% 4.67/4.91            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 4.67/4.91        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91            != (k2_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['81', '82'])).
% 4.67/4.91  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('85', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['55', '56'])).
% 4.67/4.91  thf('86', plain,
% 4.67/4.91      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['70', '75'])).
% 4.67/4.91  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('88', plain,
% 4.67/4.91      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91         (k1_zfmisc_1 @ 
% 4.67/4.91          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 4.67/4.91        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 4.67/4.91  thf('89', plain,
% 4.67/4.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['88'])).
% 4.67/4.91  thf('90', plain,
% 4.67/4.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.67/4.91         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 4.67/4.91          | ~ (v2_funct_1 @ X31)
% 4.67/4.91          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 4.67/4.91          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 4.67/4.91          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 4.67/4.91          | ~ (v1_funct_1 @ X31))),
% 4.67/4.91      inference('cnf', [status(esa)], [d4_tops_2])).
% 4.67/4.91  thf('91', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.67/4.91             (k1_relat_1 @ sk_C))
% 4.67/4.91        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['89', '90'])).
% 4.67/4.91  thf('92', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.67/4.91      inference('demod', [status(thm)], ['43', '44'])).
% 4.67/4.91  thf('93', plain,
% 4.67/4.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X24)
% 4.67/4.91          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.67/4.91          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 4.67/4.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.67/4.91          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.67/4.91          | ~ (v1_funct_1 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.67/4.91  thf('94', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91            != (k2_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['92', '93'])).
% 4.67/4.91  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('96', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['55', '56'])).
% 4.67/4.91  thf('97', plain,
% 4.67/4.91      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['70', '75'])).
% 4.67/4.91  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('99', plain,
% 4.67/4.91      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 4.67/4.91  thf('100', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['99'])).
% 4.67/4.91  thf('101', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.67/4.91      inference('demod', [status(thm)], ['43', '44'])).
% 4.67/4.91  thf('102', plain,
% 4.67/4.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X24)
% 4.67/4.91          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.67/4.91          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 4.67/4.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.67/4.91          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.67/4.91          | ~ (v1_funct_1 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.67/4.91  thf('103', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.67/4.91           (k1_relat_1 @ sk_C))
% 4.67/4.91        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91            != (k2_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['101', '102'])).
% 4.67/4.91  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('105', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['55', '56'])).
% 4.67/4.91  thf('106', plain,
% 4.67/4.91      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['70', '75'])).
% 4.67/4.91  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('108', plain,
% 4.67/4.91      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.67/4.91         (k1_relat_1 @ sk_C))
% 4.67/4.91        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 4.67/4.91  thf('109', plain,
% 4.67/4.91      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.67/4.91        (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['108'])).
% 4.67/4.91  thf('110', plain,
% 4.67/4.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['88'])).
% 4.67/4.91  thf('111', plain,
% 4.67/4.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.67/4.91         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 4.67/4.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.67/4.91  thf('112', plain,
% 4.67/4.91      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['110', '111'])).
% 4.67/4.91  thf('113', plain,
% 4.67/4.91      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['91', '100', '109', '112'])).
% 4.67/4.91  thf(t65_funct_1, axiom,
% 4.67/4.91    (![A:$i]:
% 4.67/4.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.67/4.91       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 4.67/4.91  thf('114', plain,
% 4.67/4.91      (![X2 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X2)
% 4.67/4.91          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 4.67/4.91          | ~ (v1_funct_1 @ X2)
% 4.67/4.91          | ~ (v1_relat_1 @ X2))),
% 4.67/4.91      inference('cnf', [status(esa)], [t65_funct_1])).
% 4.67/4.91  thf(t55_funct_1, axiom,
% 4.67/4.91    (![A:$i]:
% 4.67/4.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.67/4.91       ( ( v2_funct_1 @ A ) =>
% 4.67/4.91         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.67/4.91           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.67/4.91  thf('115', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X0)
% 4.67/4.91          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.67/4.91          | ~ (v1_funct_1 @ X0)
% 4.67/4.91          | ~ (v1_relat_1 @ X0))),
% 4.67/4.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.67/4.91  thf('116', plain,
% 4.67/4.91      (![X1 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X1)
% 4.67/4.91          | (v2_funct_1 @ (k2_funct_1 @ X1))
% 4.67/4.91          | ~ (v1_funct_1 @ X1)
% 4.67/4.91          | ~ (v1_relat_1 @ X1))),
% 4.67/4.91      inference('cnf', [status(esa)], [t62_funct_1])).
% 4.67/4.91  thf('117', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.67/4.91  thf('118', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('119', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('clc', [status(thm)], ['26', '27'])).
% 4.67/4.91  thf('120', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('demod', [status(thm)], ['118', '119'])).
% 4.67/4.91  thf('121', plain,
% 4.67/4.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X24)
% 4.67/4.91          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.67/4.91          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 4.67/4.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.67/4.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.67/4.91          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.67/4.91          | ~ (v1_funct_1 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.67/4.91  thf('122', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.67/4.91        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91           (k1_zfmisc_1 @ 
% 4.67/4.91            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 4.67/4.91        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.67/4.91            != (u1_struct_0 @ sk_B))
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['120', '121'])).
% 4.67/4.91  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('124', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('125', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('clc', [status(thm)], ['26', '27'])).
% 4.67/4.91  thf('126', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.67/4.91      inference('demod', [status(thm)], ['124', '125'])).
% 4.67/4.91  thf('127', plain,
% 4.67/4.91      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['29', '30'])).
% 4.67/4.91  thf('128', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('clc', [status(thm)], ['26', '27'])).
% 4.67/4.91  thf('129', plain,
% 4.67/4.91      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['127', '128'])).
% 4.67/4.91  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('131', plain,
% 4.67/4.91      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91         (k1_zfmisc_1 @ 
% 4.67/4.91          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 4.67/4.91        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.67/4.91      inference('demod', [status(thm)], ['122', '123', '126', '129', '130'])).
% 4.67/4.91  thf('132', plain,
% 4.67/4.91      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.67/4.91        | ~ (l1_struct_0 @ sk_B)
% 4.67/4.91        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91           (k1_zfmisc_1 @ 
% 4.67/4.91            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['117', '131'])).
% 4.67/4.91  thf('133', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['31', '32'])).
% 4.67/4.91  thf('134', plain, ((l1_struct_0 @ sk_B)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('135', plain,
% 4.67/4.91      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.67/4.91        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91           (k1_zfmisc_1 @ 
% 4.67/4.91            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 4.67/4.91      inference('demod', [status(thm)], ['132', '133', '134'])).
% 4.67/4.91  thf('136', plain,
% 4.67/4.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['135'])).
% 4.67/4.91  thf('137', plain,
% 4.67/4.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X24)
% 4.67/4.91          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.67/4.91          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 4.67/4.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.67/4.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.67/4.91          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.67/4.91          | ~ (v1_funct_1 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.67/4.91  thf('138', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91             (k1_relat_1 @ sk_C))
% 4.67/4.91        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_zfmisc_1 @ 
% 4.67/4.91            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.67/4.91        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['136', '137'])).
% 4.67/4.91  thf('139', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['99'])).
% 4.67/4.91  thf('140', plain,
% 4.67/4.91      (![X27 : $i]:
% 4.67/4.91         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.67/4.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.67/4.91  thf('141', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('demod', [status(thm)], ['118', '119'])).
% 4.67/4.91  thf('142', plain,
% 4.67/4.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X24)
% 4.67/4.91          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.67/4.91          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 4.67/4.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.67/4.91          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.67/4.91          | ~ (v1_funct_1 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.67/4.91  thf('143', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.67/4.91        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91           (k1_relat_1 @ sk_C))
% 4.67/4.91        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.67/4.91            != (u1_struct_0 @ sk_B))
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['141', '142'])).
% 4.67/4.91  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('145', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.67/4.91      inference('demod', [status(thm)], ['124', '125'])).
% 4.67/4.91  thf('146', plain,
% 4.67/4.91      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.67/4.91         = (k2_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['127', '128'])).
% 4.67/4.91  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('148', plain,
% 4.67/4.91      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91         (k1_relat_1 @ sk_C))
% 4.67/4.91        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.67/4.91      inference('demod', [status(thm)], ['143', '144', '145', '146', '147'])).
% 4.67/4.91  thf('149', plain,
% 4.67/4.91      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.67/4.91        | ~ (l1_struct_0 @ sk_B)
% 4.67/4.91        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91           (k1_relat_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['140', '148'])).
% 4.67/4.91  thf('150', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.67/4.91      inference('sup+', [status(thm)], ['31', '32'])).
% 4.67/4.91  thf('151', plain, ((l1_struct_0 @ sk_B)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('152', plain,
% 4.67/4.91      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91           (k1_relat_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['149', '150', '151'])).
% 4.67/4.91  thf('153', plain,
% 4.67/4.91      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91        (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['152'])).
% 4.67/4.91  thf('154', plain,
% 4.67/4.91      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91         (k1_zfmisc_1 @ 
% 4.67/4.91          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.67/4.91        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['138', '139', '153'])).
% 4.67/4.91  thf('155', plain,
% 4.67/4.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['135'])).
% 4.67/4.91  thf('156', plain,
% 4.67/4.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.67/4.91         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 4.67/4.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.67/4.91  thf('157', plain,
% 4.67/4.91      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['155', '156'])).
% 4.67/4.91  thf('158', plain,
% 4.67/4.91      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91         (k1_zfmisc_1 @ 
% 4.67/4.91          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.67/4.91        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['154', '157'])).
% 4.67/4.91  thf('159', plain,
% 4.67/4.91      ((~ (v1_relat_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_zfmisc_1 @ 
% 4.67/4.91            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['116', '158'])).
% 4.67/4.91  thf('160', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf(cc1_relset_1, axiom,
% 4.67/4.91    (![A:$i,B:$i,C:$i]:
% 4.67/4.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.67/4.91       ( v1_relat_1 @ C ) ))).
% 4.67/4.91  thf('161', plain,
% 4.67/4.91      (![X3 : $i, X4 : $i, X5 : $i]:
% 4.67/4.91         ((v1_relat_1 @ X3)
% 4.67/4.91          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 4.67/4.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.67/4.91  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 4.67/4.91      inference('sup-', [status(thm)], ['160', '161'])).
% 4.67/4.91  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('165', plain,
% 4.67/4.91      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_zfmisc_1 @ 
% 4.67/4.91            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.67/4.91      inference('demod', [status(thm)], ['159', '162', '163', '164'])).
% 4.67/4.91  thf('166', plain,
% 4.67/4.91      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v1_relat_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_zfmisc_1 @ 
% 4.67/4.91            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['115', '165'])).
% 4.67/4.91  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 4.67/4.91      inference('sup-', [status(thm)], ['160', '161'])).
% 4.67/4.91  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('170', plain,
% 4.67/4.91      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_zfmisc_1 @ 
% 4.67/4.91            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.67/4.91      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 4.67/4.91  thf('171', plain,
% 4.67/4.91      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['170'])).
% 4.67/4.91  thf('172', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('demod', [status(thm)], ['118', '119'])).
% 4.67/4.91  thf(redefinition_r2_funct_2, axiom,
% 4.67/4.91    (![A:$i,B:$i,C:$i,D:$i]:
% 4.67/4.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.67/4.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.67/4.91         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.67/4.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.67/4.91       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.67/4.91  thf('173', plain,
% 4.67/4.91      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 4.67/4.91         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 4.67/4.91          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 4.67/4.91          | ~ (v1_funct_1 @ X20)
% 4.67/4.91          | ~ (v1_funct_1 @ X23)
% 4.67/4.91          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 4.67/4.91          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 4.67/4.91          | ((X20) = (X23))
% 4.67/4.91          | ~ (r2_funct_2 @ X21 @ X22 @ X20 @ X23))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 4.67/4.91  thf('174', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.67/4.91             X0)
% 4.67/4.91          | ((sk_C) = (X0))
% 4.67/4.91          | ~ (m1_subset_1 @ X0 @ 
% 4.67/4.91               (k1_zfmisc_1 @ 
% 4.67/4.91                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.67/4.91          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.67/4.91          | ~ (v1_funct_1 @ X0)
% 4.67/4.91          | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['172', '173'])).
% 4.67/4.91  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('176', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.67/4.91      inference('demod', [status(thm)], ['124', '125'])).
% 4.67/4.91  thf('177', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.67/4.91             X0)
% 4.67/4.91          | ((sk_C) = (X0))
% 4.67/4.91          | ~ (m1_subset_1 @ X0 @ 
% 4.67/4.91               (k1_zfmisc_1 @ 
% 4.67/4.91                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.67/4.91          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.67/4.91          | ~ (v1_funct_1 @ X0))),
% 4.67/4.91      inference('demod', [status(thm)], ['174', '175', '176'])).
% 4.67/4.91  thf('178', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.67/4.91        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91             (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.67/4.91        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.67/4.91        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.67/4.91             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['171', '177'])).
% 4.67/4.91  thf('179', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X0)
% 4.67/4.91          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.67/4.91          | ~ (v1_funct_1 @ X0)
% 4.67/4.91          | ~ (v1_relat_1 @ X0))),
% 4.67/4.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.67/4.91  thf('180', plain,
% 4.67/4.91      (![X1 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X1)
% 4.67/4.91          | (v2_funct_1 @ (k2_funct_1 @ X1))
% 4.67/4.91          | ~ (v1_funct_1 @ X1)
% 4.67/4.91          | ~ (v1_relat_1 @ X1))),
% 4.67/4.91      inference('cnf', [status(esa)], [t62_funct_1])).
% 4.67/4.91  thf('181', plain,
% 4.67/4.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['135'])).
% 4.67/4.91  thf('182', plain,
% 4.67/4.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X24)
% 4.67/4.91          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.67/4.91          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 4.67/4.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.67/4.91          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.67/4.91          | ~ (v1_funct_1 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.67/4.91  thf('183', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91             (k1_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.67/4.91        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['181', '182'])).
% 4.67/4.91  thf('184', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['99'])).
% 4.67/4.91  thf('185', plain,
% 4.67/4.91      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91        (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['152'])).
% 4.67/4.91  thf('186', plain,
% 4.67/4.91      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.67/4.91        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['183', '184', '185'])).
% 4.67/4.91  thf('187', plain,
% 4.67/4.91      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['155', '156'])).
% 4.67/4.91  thf('188', plain,
% 4.67/4.91      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.67/4.91        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['186', '187'])).
% 4.67/4.91  thf('189', plain,
% 4.67/4.91      ((~ (v1_relat_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['180', '188'])).
% 4.67/4.91  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 4.67/4.91      inference('sup-', [status(thm)], ['160', '161'])).
% 4.67/4.91  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('193', plain,
% 4.67/4.91      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.67/4.91      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 4.67/4.91  thf('194', plain,
% 4.67/4.91      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v1_relat_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['179', '193'])).
% 4.67/4.91  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 4.67/4.91      inference('sup-', [status(thm)], ['160', '161'])).
% 4.67/4.91  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('198', plain,
% 4.67/4.91      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.67/4.91      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 4.67/4.91  thf('199', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('simplify', [status(thm)], ['198'])).
% 4.67/4.91  thf('200', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X0)
% 4.67/4.91          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.67/4.91          | ~ (v1_funct_1 @ X0)
% 4.67/4.91          | ~ (v1_relat_1 @ X0))),
% 4.67/4.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.67/4.91  thf('201', plain,
% 4.67/4.91      (![X1 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X1)
% 4.67/4.91          | (v2_funct_1 @ (k2_funct_1 @ X1))
% 4.67/4.91          | ~ (v1_funct_1 @ X1)
% 4.67/4.91          | ~ (v1_relat_1 @ X1))),
% 4.67/4.91      inference('cnf', [status(esa)], [t62_funct_1])).
% 4.67/4.91  thf('202', plain,
% 4.67/4.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['135'])).
% 4.67/4.91  thf('203', plain,
% 4.67/4.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X24)
% 4.67/4.91          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.67/4.91          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 4.67/4.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.67/4.91          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.67/4.91          | ~ (v1_funct_1 @ X24))),
% 4.67/4.91      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.67/4.91  thf('204', plain,
% 4.67/4.91      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91             (k1_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.67/4.91        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['202', '203'])).
% 4.67/4.91  thf('205', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['99'])).
% 4.67/4.91  thf('206', plain,
% 4.67/4.91      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.67/4.91        (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['152'])).
% 4.67/4.91  thf('207', plain,
% 4.67/4.91      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.67/4.91        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['204', '205', '206'])).
% 4.67/4.91  thf('208', plain,
% 4.67/4.91      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['155', '156'])).
% 4.67/4.91  thf('209', plain,
% 4.67/4.91      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.67/4.91        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['207', '208'])).
% 4.67/4.91  thf('210', plain,
% 4.67/4.91      ((~ (v1_relat_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['201', '209'])).
% 4.67/4.91  thf('211', plain, ((v1_relat_1 @ sk_C)),
% 4.67/4.91      inference('sup-', [status(thm)], ['160', '161'])).
% 4.67/4.91  thf('212', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('213', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('214', plain,
% 4.67/4.91      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.67/4.91      inference('demod', [status(thm)], ['210', '211', '212', '213'])).
% 4.67/4.91  thf('215', plain,
% 4.67/4.91      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v1_relat_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['200', '214'])).
% 4.67/4.91  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 4.67/4.91      inference('sup-', [status(thm)], ['160', '161'])).
% 4.67/4.91  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('219', plain,
% 4.67/4.91      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.67/4.91        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.67/4.91      inference('demod', [status(thm)], ['215', '216', '217', '218'])).
% 4.67/4.91  thf('220', plain,
% 4.67/4.91      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.67/4.91        (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.67/4.91      inference('simplify', [status(thm)], ['219'])).
% 4.67/4.91  thf('221', plain,
% 4.67/4.91      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.67/4.91        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.67/4.91             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.67/4.91      inference('demod', [status(thm)], ['178', '199', '220'])).
% 4.67/4.91  thf('222', plain,
% 4.67/4.91      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.67/4.91           sk_C)
% 4.67/4.91        | ~ (v1_relat_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.67/4.91      inference('sup-', [status(thm)], ['114', '221'])).
% 4.67/4.91  thf('223', plain,
% 4.67/4.91      ((m1_subset_1 @ sk_C @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.67/4.91      inference('demod', [status(thm)], ['118', '119'])).
% 4.67/4.91  thf('224', plain,
% 4.67/4.91      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 4.67/4.91         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 4.67/4.91          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 4.67/4.91          | ~ (v1_funct_1 @ X20)
% 4.67/4.91          | ~ (v1_funct_1 @ X23)
% 4.67/4.91          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 4.67/4.91          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 4.67/4.91          | (r2_funct_2 @ X21 @ X22 @ X20 @ X23)
% 4.67/4.91          | ((X20) != (X23)))),
% 4.67/4.91      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 4.67/4.91  thf('225', plain,
% 4.67/4.91      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.67/4.91         ((r2_funct_2 @ X21 @ X22 @ X23 @ X23)
% 4.67/4.91          | ~ (v1_funct_1 @ X23)
% 4.67/4.91          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 4.67/4.91          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['224'])).
% 4.67/4.91  thf('226', plain,
% 4.67/4.91      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.67/4.91           sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['223', '225'])).
% 4.67/4.91  thf('227', plain,
% 4.67/4.91      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.67/4.91      inference('demod', [status(thm)], ['124', '125'])).
% 4.67/4.91  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('229', plain,
% 4.67/4.91      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 4.67/4.91      inference('demod', [status(thm)], ['226', '227', '228'])).
% 4.67/4.91  thf('230', plain, ((v1_relat_1 @ sk_C)),
% 4.67/4.91      inference('sup-', [status(thm)], ['160', '161'])).
% 4.67/4.91  thf('231', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('232', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('233', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['222', '229', '230', '231', '232'])).
% 4.67/4.91  thf('234', plain,
% 4.67/4.91      (![X1 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X1)
% 4.67/4.91          | (v2_funct_1 @ (k2_funct_1 @ X1))
% 4.67/4.91          | ~ (v1_funct_1 @ X1)
% 4.67/4.91          | ~ (v1_relat_1 @ X1))),
% 4.67/4.91      inference('cnf', [status(esa)], [t62_funct_1])).
% 4.67/4.91  thf('235', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['222', '229', '230', '231', '232'])).
% 4.67/4.91  thf('236', plain,
% 4.67/4.91      (![X0 : $i]:
% 4.67/4.91         (~ (v2_funct_1 @ X0)
% 4.67/4.91          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 4.67/4.91          | ~ (v1_funct_1 @ X0)
% 4.67/4.91          | ~ (v1_relat_1 @ X0))),
% 4.67/4.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.67/4.91  thf('237', plain,
% 4.67/4.91      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('sup+', [status(thm)], ['235', '236'])).
% 4.67/4.91  thf('238', plain,
% 4.67/4.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.67/4.91        (k1_zfmisc_1 @ 
% 4.67/4.91         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.67/4.91      inference('simplify', [status(thm)], ['88'])).
% 4.67/4.91  thf('239', plain,
% 4.67/4.91      (![X3 : $i, X4 : $i, X5 : $i]:
% 4.67/4.91         ((v1_relat_1 @ X3)
% 4.67/4.91          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 4.67/4.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.67/4.91  thf('240', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.67/4.91      inference('sup-', [status(thm)], ['238', '239'])).
% 4.67/4.91  thf('241', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.67/4.91      inference('simplify', [status(thm)], ['99'])).
% 4.67/4.91  thf('242', plain,
% 4.67/4.91      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['237', '240', '241'])).
% 4.67/4.91  thf('243', plain,
% 4.67/4.91      ((~ (v1_relat_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['234', '242'])).
% 4.67/4.91  thf('244', plain, ((v1_relat_1 @ sk_C)),
% 4.67/4.91      inference('sup-', [status(thm)], ['160', '161'])).
% 4.67/4.91  thf('245', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('246', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('247', plain,
% 4.67/4.91      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['243', '244', '245', '246'])).
% 4.67/4.91  thf('248', plain,
% 4.67/4.91      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91          (k2_funct_1 @ sk_C)) = (sk_C))
% 4.67/4.91        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 4.67/4.91      inference('demod', [status(thm)], ['113', '233', '247'])).
% 4.67/4.91  thf('249', plain,
% 4.67/4.91      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.67/4.91        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 4.67/4.91      inference('simplify', [status(thm)], ['248'])).
% 4.67/4.91  thf('250', plain,
% 4.67/4.91      ((~ (v1_relat_1 @ sk_C)
% 4.67/4.91        | ~ (v1_funct_1 @ sk_C)
% 4.67/4.91        | ~ (v2_funct_1 @ sk_C)
% 4.67/4.91        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 4.67/4.91      inference('sup-', [status(thm)], ['80', '249'])).
% 4.67/4.91  thf('251', plain, ((v1_relat_1 @ sk_C)),
% 4.67/4.91      inference('sup-', [status(thm)], ['160', '161'])).
% 4.67/4.91  thf('252', plain, ((v1_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('253', plain, ((v2_funct_1 @ sk_C)),
% 4.67/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.67/4.91  thf('254', plain,
% 4.67/4.91      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.67/4.91         (k2_funct_1 @ sk_C)) = (sk_C))),
% 4.67/4.91      inference('demod', [status(thm)], ['250', '251', '252', '253'])).
% 4.67/4.91  thf('255', plain,
% 4.67/4.91      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 4.67/4.91      inference('demod', [status(thm)], ['226', '227', '228'])).
% 4.67/4.91  thf('256', plain, ($false),
% 4.67/4.91      inference('demod', [status(thm)], ['79', '254', '255'])).
% 4.67/4.91  
% 4.67/4.91  % SZS output end Refutation
% 4.67/4.91  
% 4.73/4.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
