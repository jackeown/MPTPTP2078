%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WNYp75qUSk

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:09 EST 2020

% Result     : Theorem 3.74s
% Output     : Refutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  516 (7615 expanded)
%              Number of leaves         :   50 (2239 expanded)
%              Depth                    :   45
%              Number of atoms          : 5389 (163715 expanded)
%              Number of equality atoms :  277 (5462 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('19',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('26',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('35',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','39'])).

thf('41',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['23','40'])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','41'])).

thf('43',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('62',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','39'])).

thf('68',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','68'])).

thf('70',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','69'])).

thf('71',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','70'])).

thf('72',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('73',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('81',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('82',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

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

thf('84',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X35 @ X37 )
       != X35 )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_tops_2 @ X36 @ X35 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','93'])).

thf('95',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','79','80','81','98'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('100',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('101',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('102',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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

thf('103',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('104',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('105',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('106',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('108',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('109',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('113',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('114',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['112','114'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('116',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('117',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('121',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C )
        = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['111','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('127',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('128',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('130',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['128','131','132'])).

thf('134',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('135',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['128','131','132'])).

thf('137',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['125','139','140','141','142'])).

thf('144',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','69'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_A )
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_struct_0 @ sk_B ) )
      | ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ ( k2_struct_0 @ sk_B ) )
      | ( ( k2_struct_0 @ sk_A )
        = ( k1_relat_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_struct_0 @ sk_B ) )
      | ( ( k2_struct_0 @ sk_A )
        = ( k1_relat_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_A )
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('154',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('155',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

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

thf('158',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('159',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('162',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('163',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('167',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('168',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','160','165','170','171'])).

thf('173',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('175',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('178',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X29 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('179',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('182',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','180','181','182','183'])).

thf('185',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('187',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['176','187'])).

thf('189',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_A )
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('191',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('192',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('193',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('194',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('195',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('198',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('199',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['195','196','197','198','199'])).

thf('201',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['192','200'])).

thf('202',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('206',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['191','206'])).

thf('208',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['190','209'])).

thf('211',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('212',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('213',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X29 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('214',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('217',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['214','215','216','217','218'])).

thf('220',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','219'])).

thf('221',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('225',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['210','225'])).

thf('227',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['189','226'])).

thf('228',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['188','229'])).

thf('231',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('233',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('237',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('238',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['236','244'])).

thf('246',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['135','138'])).

thf('247',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('248',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('250',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['245','246','247','248','249'])).

thf('251',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','69'])).

thf('252',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('254',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('256',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['257','258'])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['235','259'])).

thf('261',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('264',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('265',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('266',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('268',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('271',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('272',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['271','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['270','273'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['269','275'])).

thf('277',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['268','277'])).

thf('279',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['267','278'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['266','280'])).

thf('282',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['265','282'])).

thf('284',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['264','284'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['285'])).

thf('287',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('288',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['263','288'])).

thf('290',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['289'])).

thf('291',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['262','290'])).

thf('292',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('293',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('294',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('295',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['291','292','293','294','295','296'])).

thf('298',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['106','297'])).

thf('299',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('300',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('301',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('302',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['300','301'])).

thf('303',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['299','303'])).

thf('305',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('306',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['304','305','306','307'])).

thf('309',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('310',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('311',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('312',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('313',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('316',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('317',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['313','314','315','316','317'])).

thf('319',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['298','310','319'])).

thf('321',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['105','320'])).

thf('322',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('323',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['321','322','323','324'])).

thf('326',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['289'])).

thf('327',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['325','326'])).

thf('328',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('329',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('330',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('331',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['328','331'])).

thf('333',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('336',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['332','333','334','335'])).

thf('337',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('338',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['318'])).

thf('339',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['327','336','337','338'])).

thf('340',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['104','339'])).

thf('341',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('342',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['340','341','342','343'])).

thf('345',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['103','344'])).

thf('346',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('347',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['285'])).

thf('348',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['346','347'])).

thf('349',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('350',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('351',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['348','349','350','351','352'])).

thf('354',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('355',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['353','354'])).

thf('356',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('357',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['318'])).

thf('358',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('359',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['302'])).

thf('360',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('361',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['359','360'])).

thf('362',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('363',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('364',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('365',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('366',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('367',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['365','366'])).

thf('368',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['364','367'])).

thf('369',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['368'])).

thf('370',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['363','369'])).

thf('371',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['362','371'])).

thf('373',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['372'])).

thf('374',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['302'])).

thf('375',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('376',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['374','375'])).

thf('377',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['373','376'])).

thf('378',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['377'])).

thf('379',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['361','378'])).

thf('380',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['379'])).

thf('381',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['358','380'])).

thf('382',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['381'])).

thf('383',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['357','382'])).

thf('384',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('385',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['383','384','385','386'])).

thf('388',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['356','387'])).

thf('389',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('390',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('391',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['388','389','390','391'])).

thf('393',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['392'])).

thf('394',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['345','355','393'])).

thf('395',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['102','394'])).

thf('396',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('398',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('400',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['395','396','397','398','399'])).

thf('401',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['101','400'])).

thf('402',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('403',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('404',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('406',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['401','402','403','404','405'])).

thf('407',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('408',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('409',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['407','408'])).

thf('410',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('411',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('412',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X35 @ X37 )
       != X35 )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_tops_2 @ X36 @ X35 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('413',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['411','412'])).

thf('414',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['413'])).

thf('415',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['410','414'])).

thf('416',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['415'])).

thf('417',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['409','416'])).

thf('418',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['417'])).

thf('419',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['406','418'])).

thf('420',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['321','322','323','324'])).

thf('421',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['318'])).

thf('422',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('423',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['419','420','421','422'])).

thf('424',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['100','423'])).

thf('425',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('426',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('427',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('428',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['424','425','426','427'])).

thf('429',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('430',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['348','349','350','351','352'])).

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

thf('431',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_funct_2 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('432',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['431'])).

thf('433',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['430','432'])).

thf('434',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('435',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('436',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('437',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('438',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('439',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('440',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['370'])).

thf('441',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['439','440'])).

thf('442',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['438','441'])).

thf('443',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['442'])).

thf('444',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['437','443'])).

thf('445',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['444'])).

thf('446',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['436','445'])).

thf('447',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['446'])).

thf('448',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['435','447'])).

thf('449',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['448'])).

thf('450',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['434','449'])).

thf('451',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('452',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('453',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('454',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['450','451','452','453'])).

thf('455',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('456',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['454','455'])).

thf('457',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['392'])).

thf('458',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['433','456','457'])).

thf('459',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['429','458'])).

thf('460',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['129','130'])).

thf('461',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('462',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('463',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['459','460','461','462'])).

thf('464',plain,(
    $false ),
    inference(demod,[status(thm)],['99','428','463'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WNYp75qUSk
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.74/4.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.74/4.01  % Solved by: fo/fo7.sh
% 3.74/4.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.74/4.01  % done 2761 iterations in 3.546s
% 3.74/4.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.74/4.01  % SZS output start Refutation
% 3.74/4.01  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.74/4.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.74/4.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.74/4.01  thf(sk_A_type, type, sk_A: $i).
% 3.74/4.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.74/4.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.74/4.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.74/4.01  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 3.74/4.01  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 3.74/4.01  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.74/4.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.74/4.01  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.74/4.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.74/4.01  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.74/4.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.74/4.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.74/4.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.74/4.01  thf(sk_B_type, type, sk_B: $i).
% 3.74/4.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.74/4.01  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.74/4.01  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.74/4.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.74/4.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.74/4.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.74/4.01  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 3.74/4.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.74/4.01  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.74/4.01  thf(sk_C_type, type, sk_C: $i).
% 3.74/4.01  thf(d3_struct_0, axiom,
% 3.74/4.01    (![A:$i]:
% 3.74/4.01     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.74/4.01  thf('0', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('1', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf(t64_tops_2, conjecture,
% 3.74/4.01    (![A:$i]:
% 3.74/4.01     ( ( l1_struct_0 @ A ) =>
% 3.74/4.01       ( ![B:$i]:
% 3.74/4.01         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.74/4.01           ( ![C:$i]:
% 3.74/4.01             ( ( ( v1_funct_1 @ C ) & 
% 3.74/4.01                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.74/4.01                 ( m1_subset_1 @
% 3.74/4.01                   C @ 
% 3.74/4.01                   ( k1_zfmisc_1 @
% 3.74/4.01                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.74/4.01               ( ( ( ( k2_relset_1 @
% 3.74/4.01                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.74/4.01                     ( k2_struct_0 @ B ) ) & 
% 3.74/4.01                   ( v2_funct_1 @ C ) ) =>
% 3.74/4.01                 ( r2_funct_2 @
% 3.74/4.01                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.74/4.01                   ( k2_tops_2 @
% 3.74/4.01                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.74/4.01                     ( k2_tops_2 @
% 3.74/4.01                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 3.74/4.01                   C ) ) ) ) ) ) ))).
% 3.74/4.01  thf(zf_stmt_0, negated_conjecture,
% 3.74/4.01    (~( ![A:$i]:
% 3.74/4.01        ( ( l1_struct_0 @ A ) =>
% 3.74/4.01          ( ![B:$i]:
% 3.74/4.01            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.74/4.01              ( ![C:$i]:
% 3.74/4.01                ( ( ( v1_funct_1 @ C ) & 
% 3.74/4.01                    ( v1_funct_2 @
% 3.74/4.01                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.74/4.01                    ( m1_subset_1 @
% 3.74/4.01                      C @ 
% 3.74/4.01                      ( k1_zfmisc_1 @
% 3.74/4.01                        ( k2_zfmisc_1 @
% 3.74/4.01                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.74/4.01                  ( ( ( ( k2_relset_1 @
% 3.74/4.01                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.74/4.01                        ( k2_struct_0 @ B ) ) & 
% 3.74/4.01                      ( v2_funct_1 @ C ) ) =>
% 3.74/4.01                    ( r2_funct_2 @
% 3.74/4.01                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.74/4.01                      ( k2_tops_2 @
% 3.74/4.01                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.74/4.01                        ( k2_tops_2 @
% 3.74/4.01                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 3.74/4.01                      C ) ) ) ) ) ) ) )),
% 3.74/4.01    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 3.74/4.01  thf('2', plain,
% 3.74/4.01      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/4.01          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.74/4.01           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/4.01          sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('3', plain,
% 3.74/4.01      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/4.01           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.74/4.01            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/4.01           sk_C)
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup-', [status(thm)], ['1', '2'])).
% 3.74/4.01  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('5', plain,
% 3.74/4.01      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.74/4.01          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.74/4.01           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/4.01          sk_C)),
% 3.74/4.01      inference('demod', [status(thm)], ['3', '4'])).
% 3.74/4.01  thf('6', plain,
% 3.74/4.01      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.01           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.74/4.01            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/4.01           sk_C)
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup-', [status(thm)], ['0', '5'])).
% 3.74/4.01  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('8', plain,
% 3.74/4.01      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.01          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.74/4.01           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 3.74/4.01          sk_C)),
% 3.74/4.01      inference('demod', [status(thm)], ['6', '7'])).
% 3.74/4.01  thf(d1_funct_2, axiom,
% 3.74/4.01    (![A:$i,B:$i,C:$i]:
% 3.74/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/4.01       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.74/4.01           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.74/4.01             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.74/4.01         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.74/4.01           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.74/4.01             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.74/4.01  thf(zf_stmt_1, axiom,
% 3.74/4.01    (![B:$i,A:$i]:
% 3.74/4.01     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.74/4.01       ( zip_tseitin_0 @ B @ A ) ))).
% 3.74/4.01  thf('9', plain,
% 3.74/4.01      (![X17 : $i, X18 : $i]:
% 3.74/4.01         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/4.01  thf('10', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.74/4.01  thf(zf_stmt_3, axiom,
% 3.74/4.01    (![C:$i,B:$i,A:$i]:
% 3.74/4.01     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.74/4.01       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.74/4.01  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.74/4.01  thf(zf_stmt_5, axiom,
% 3.74/4.01    (![A:$i,B:$i,C:$i]:
% 3.74/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/4.01       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.74/4.01         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.74/4.01           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.74/4.01             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.74/4.01  thf('11', plain,
% 3.74/4.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.74/4.01         (~ (zip_tseitin_0 @ X22 @ X23)
% 3.74/4.01          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 3.74/4.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/4.01  thf('12', plain,
% 3.74/4.01      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.74/4.01        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['10', '11'])).
% 3.74/4.01  thf('13', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/4.01        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['9', '12'])).
% 3.74/4.01  thf('14', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('15', plain,
% 3.74/4.01      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.74/4.01         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 3.74/4.01          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 3.74/4.01          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.74/4.01  thf('16', plain,
% 3.74/4.01      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.74/4.01        | ((u1_struct_0 @ sk_A)
% 3.74/4.01            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['14', '15'])).
% 3.74/4.01  thf('17', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf(t38_relset_1, axiom,
% 3.74/4.01    (![A:$i,B:$i,C:$i]:
% 3.74/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/4.01       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 3.74/4.01         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.74/4.01  thf('18', plain,
% 3.74/4.01      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.74/4.01         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 3.74/4.01            = (k1_relset_1 @ X14 @ X15 @ X16))
% 3.74/4.01          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.74/4.01      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/4.01  thf('19', plain,
% 3.74/4.01      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/4.01         (u1_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['17', '18'])).
% 3.74/4.01  thf('20', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf(redefinition_k8_relset_1, axiom,
% 3.74/4.01    (![A:$i,B:$i,C:$i,D:$i]:
% 3.74/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/4.01       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 3.74/4.01  thf('21', plain,
% 3.74/4.01      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.74/4.01         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 3.74/4.01          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 3.74/4.01      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.74/4.01  thf('22', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/4.01           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.74/4.01      inference('sup-', [status(thm)], ['20', '21'])).
% 3.74/4.01  thf('23', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('demod', [status(thm)], ['19', '22'])).
% 3.74/4.01  thf('24', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('25', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('demod', [status(thm)], ['19', '22'])).
% 3.74/4.01  thf('26', plain,
% 3.74/4.01      ((((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/4.01          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['24', '25'])).
% 3.74/4.01  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('28', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('demod', [status(thm)], ['26', '27'])).
% 3.74/4.01  thf('29', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('30', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('31', plain,
% 3.74/4.01      (((m1_subset_1 @ sk_C @ 
% 3.74/4.01         (k1_zfmisc_1 @ 
% 3.74/4.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['29', '30'])).
% 3.74/4.01  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('33', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['31', '32'])).
% 3.74/4.01  thf('34', plain,
% 3.74/4.01      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.74/4.01         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 3.74/4.01            = (k1_relset_1 @ X14 @ X15 @ X16))
% 3.74/4.01          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.74/4.01      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/4.01  thf('35', plain,
% 3.74/4.01      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.74/4.01         (k2_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['33', '34'])).
% 3.74/4.01  thf('36', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['31', '32'])).
% 3.74/4.01  thf('37', plain,
% 3.74/4.01      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.74/4.01         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 3.74/4.01          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 3.74/4.01      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.74/4.01  thf('38', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.74/4.01           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.74/4.01      inference('sup-', [status(thm)], ['36', '37'])).
% 3.74/4.01  thf('39', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('demod', [status(thm)], ['35', '38'])).
% 3.74/4.01  thf('40', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/4.01         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['28', '39'])).
% 3.74/4.01  thf('41', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('demod', [status(thm)], ['23', '40'])).
% 3.74/4.01  thf('42', plain,
% 3.74/4.01      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.74/4.01        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['16', '41'])).
% 3.74/4.01  thf('43', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/4.01        | ((u1_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['13', '42'])).
% 3.74/4.01  thf('44', plain,
% 3.74/4.01      (![X17 : $i, X18 : $i]:
% 3.74/4.01         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/4.01  thf('45', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('46', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('47', plain,
% 3.74/4.01      (((m1_subset_1 @ sk_C @ 
% 3.74/4.01         (k1_zfmisc_1 @ 
% 3.74/4.01          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_A))),
% 3.74/4.01      inference('sup+', [status(thm)], ['45', '46'])).
% 3.74/4.01  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('49', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['47', '48'])).
% 3.74/4.01  thf('50', plain,
% 3.74/4.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.74/4.01         (~ (zip_tseitin_0 @ X22 @ X23)
% 3.74/4.01          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 3.74/4.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/4.01  thf('51', plain,
% 3.74/4.01      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/4.01        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['49', '50'])).
% 3.74/4.01  thf('52', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/4.01        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['44', '51'])).
% 3.74/4.01  thf('53', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('54', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('55', plain,
% 3.74/4.01      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_A))),
% 3.74/4.01      inference('sup+', [status(thm)], ['53', '54'])).
% 3.74/4.01  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('57', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['55', '56'])).
% 3.74/4.01  thf('58', plain,
% 3.74/4.01      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.74/4.01         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 3.74/4.01          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 3.74/4.01          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.74/4.01  thf('59', plain,
% 3.74/4.01      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/4.01        | ((k2_struct_0 @ sk_A)
% 3.74/4.01            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['57', '58'])).
% 3.74/4.01  thf('60', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['47', '48'])).
% 3.74/4.01  thf('61', plain,
% 3.74/4.01      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.74/4.01         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 3.74/4.01            = (k1_relset_1 @ X14 @ X15 @ X16))
% 3.74/4.01          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.74/4.01      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/4.01  thf('62', plain,
% 3.74/4.01      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/4.01         (u1_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['60', '61'])).
% 3.74/4.01  thf('63', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['47', '48'])).
% 3.74/4.01  thf('64', plain,
% 3.74/4.01      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.74/4.01         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 3.74/4.01          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 3.74/4.01      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.74/4.01  thf('65', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 3.74/4.01           X0) = (k10_relat_1 @ sk_C @ X0))),
% 3.74/4.01      inference('sup-', [status(thm)], ['63', '64'])).
% 3.74/4.01  thf('66', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('demod', [status(thm)], ['62', '65'])).
% 3.74/4.01  thf('67', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/4.01         = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['28', '39'])).
% 3.74/4.01  thf('68', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('demod', [status(thm)], ['66', '67'])).
% 3.74/4.01  thf('69', plain,
% 3.74/4.01      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['59', '68'])).
% 3.74/4.01  thf('70', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['52', '69'])).
% 3.74/4.01  thf('71', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 3.74/4.01        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/4.01        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['43', '70'])).
% 3.74/4.01  thf('72', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 3.74/4.01      inference('simplify', [status(thm)], ['71'])).
% 3.74/4.01  thf(fc2_struct_0, axiom,
% 3.74/4.01    (![A:$i]:
% 3.74/4.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.74/4.01       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.74/4.01  thf('73', plain,
% 3.74/4.01      (![X34 : $i]:
% 3.74/4.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 3.74/4.01          | ~ (l1_struct_0 @ X34)
% 3.74/4.01          | (v2_struct_0 @ X34))),
% 3.74/4.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.74/4.01  thf('74', plain,
% 3.74/4.01      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 3.74/4.01        | (v2_struct_0 @ sk_B)
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup-', [status(thm)], ['72', '73'])).
% 3.74/4.01  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.74/4.01  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.74/4.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.74/4.01  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('77', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['74', '75', '76'])).
% 3.74/4.01  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('79', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.74/4.01      inference('clc', [status(thm)], ['77', '78'])).
% 3.74/4.01  thf('80', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.74/4.01      inference('clc', [status(thm)], ['77', '78'])).
% 3.74/4.01  thf('81', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 3.74/4.01      inference('clc', [status(thm)], ['77', '78'])).
% 3.74/4.01  thf('82', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('83', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['47', '48'])).
% 3.74/4.01  thf(d4_tops_2, axiom,
% 3.74/4.01    (![A:$i,B:$i,C:$i]:
% 3.74/4.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.74/4.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.74/4.01       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.74/4.01         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 3.74/4.01  thf('84', plain,
% 3.74/4.01      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.74/4.01         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 3.74/4.01          | ~ (v2_funct_1 @ X37)
% 3.74/4.01          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 3.74/4.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 3.74/4.01          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 3.74/4.01          | ~ (v1_funct_1 @ X37))),
% 3.74/4.01      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.74/4.01  thf('85', plain,
% 3.74/4.01      ((~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/4.01        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01            = (k2_funct_1 @ sk_C))
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C)
% 3.74/4.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01            != (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['83', '84'])).
% 3.74/4.01  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('87', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['55', '56'])).
% 3.74/4.01  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('89', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('90', plain,
% 3.74/4.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('91', plain,
% 3.74/4.01      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01          = (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_A))),
% 3.74/4.01      inference('sup+', [status(thm)], ['89', '90'])).
% 3.74/4.01  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('93', plain,
% 3.74/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['91', '92'])).
% 3.74/4.01  thf('94', plain,
% 3.74/4.01      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01          = (k2_funct_1 @ sk_C))
% 3.74/4.01        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('demod', [status(thm)], ['85', '86', '87', '88', '93'])).
% 3.74/4.01  thf('95', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B)
% 3.74/4.01        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01            = (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['82', '94'])).
% 3.74/4.01  thf('96', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('97', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/4.01        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01            = (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('demod', [status(thm)], ['95', '96'])).
% 3.74/4.01  thf('98', plain,
% 3.74/4.01      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_funct_1 @ sk_C))),
% 3.74/4.01      inference('simplify', [status(thm)], ['97'])).
% 3.74/4.01  thf('99', plain,
% 3.74/4.01      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.01          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01           (k2_funct_1 @ sk_C)) @ 
% 3.74/4.01          sk_C)),
% 3.74/4.01      inference('demod', [status(thm)], ['8', '79', '80', '81', '98'])).
% 3.74/4.01  thf(fc6_funct_1, axiom,
% 3.74/4.01    (![A:$i]:
% 3.74/4.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 3.74/4.01       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.74/4.01         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 3.74/4.01         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.74/4.01  thf('100', plain,
% 3.74/4.01      (![X1 : $i]:
% 3.74/4.01         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 3.74/4.01          | ~ (v2_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_relat_1 @ X1))),
% 3.74/4.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/4.01  thf(t65_funct_1, axiom,
% 3.74/4.01    (![A:$i]:
% 3.74/4.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.74/4.01       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 3.74/4.01  thf('101', plain,
% 3.74/4.01      (![X3 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X3)
% 3.74/4.01          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 3.74/4.01          | ~ (v1_funct_1 @ X3)
% 3.74/4.01          | ~ (v1_relat_1 @ X3))),
% 3.74/4.01      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.74/4.01  thf('102', plain,
% 3.74/4.01      (![X3 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X3)
% 3.74/4.01          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 3.74/4.01          | ~ (v1_funct_1 @ X3)
% 3.74/4.01          | ~ (v1_relat_1 @ X3))),
% 3.74/4.01      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.74/4.01  thf(t55_funct_1, axiom,
% 3.74/4.01    (![A:$i]:
% 3.74/4.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.74/4.01       ( ( v2_funct_1 @ A ) =>
% 3.74/4.01         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.74/4.01           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.74/4.01  thf('103', plain,
% 3.74/4.01      (![X2 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X2)
% 3.74/4.01          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 3.74/4.01          | ~ (v1_funct_1 @ X2)
% 3.74/4.01          | ~ (v1_relat_1 @ X2))),
% 3.74/4.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.74/4.01  thf('104', plain,
% 3.74/4.01      (![X1 : $i]:
% 3.74/4.01         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 3.74/4.01          | ~ (v2_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_relat_1 @ X1))),
% 3.74/4.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/4.01  thf('105', plain,
% 3.74/4.01      (![X1 : $i]:
% 3.74/4.01         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 3.74/4.01          | ~ (v2_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_relat_1 @ X1))),
% 3.74/4.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/4.01  thf('106', plain,
% 3.74/4.01      (![X2 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X2)
% 3.74/4.01          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 3.74/4.01          | ~ (v1_funct_1 @ X2)
% 3.74/4.01          | ~ (v1_relat_1 @ X2))),
% 3.74/4.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.74/4.01  thf('107', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf(redefinition_k2_relset_1, axiom,
% 3.74/4.01    (![A:$i,B:$i,C:$i]:
% 3.74/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/4.01       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.74/4.01  thf('108', plain,
% 3.74/4.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.74/4.01         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 3.74/4.01          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.74/4.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.74/4.01  thf('109', plain,
% 3.74/4.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_relat_1 @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['107', '108'])).
% 3.74/4.01  thf('110', plain,
% 3.74/4.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('111', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.01  thf('112', plain,
% 3.74/4.01      (![X17 : $i, X18 : $i]:
% 3.74/4.01         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/4.01  thf('113', plain,
% 3.74/4.01      (![X17 : $i, X18 : $i]:
% 3.74/4.01         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/4.01  thf('114', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 3.74/4.01      inference('simplify', [status(thm)], ['113'])).
% 3.74/4.01  thf('115', plain,
% 3.74/4.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.74/4.01         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 3.74/4.01      inference('sup+', [status(thm)], ['112', '114'])).
% 3.74/4.01  thf(t3_funct_2, axiom,
% 3.74/4.01    (![A:$i]:
% 3.74/4.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.74/4.01       ( ( v1_funct_1 @ A ) & 
% 3.74/4.01         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 3.74/4.01         ( m1_subset_1 @
% 3.74/4.01           A @ 
% 3.74/4.01           ( k1_zfmisc_1 @
% 3.74/4.01             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.74/4.01  thf('116', plain,
% 3.74/4.01      (![X32 : $i]:
% 3.74/4.01         ((m1_subset_1 @ X32 @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 3.74/4.01          | ~ (v1_funct_1 @ X32)
% 3.74/4.01          | ~ (v1_relat_1 @ X32))),
% 3.74/4.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.74/4.01  thf('117', plain,
% 3.74/4.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.74/4.01         (~ (zip_tseitin_0 @ X22 @ X23)
% 3.74/4.01          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 3.74/4.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/4.01  thf('118', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['116', '117'])).
% 3.74/4.01  thf('119', plain,
% 3.74/4.01      (![X0 : $i, X1 : $i]:
% 3.74/4.01         ((zip_tseitin_0 @ X1 @ (k2_relat_1 @ X0))
% 3.74/4.01          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('sup-', [status(thm)], ['115', '118'])).
% 3.74/4.01  thf('120', plain,
% 3.74/4.01      (![X32 : $i]:
% 3.74/4.01         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 3.74/4.01          | ~ (v1_funct_1 @ X32)
% 3.74/4.01          | ~ (v1_relat_1 @ X32))),
% 3.74/4.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.74/4.01  thf('121', plain,
% 3.74/4.01      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.74/4.01         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 3.74/4.01          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 3.74/4.01          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.74/4.01  thf('122', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.74/4.01          | ((k1_relat_1 @ X0)
% 3.74/4.01              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['120', '121'])).
% 3.74/4.01  thf('123', plain,
% 3.74/4.01      (![X0 : $i, X1 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | (zip_tseitin_0 @ X1 @ (k2_relat_1 @ X0))
% 3.74/4.01          | ((k1_relat_1 @ X0)
% 3.74/4.01              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('sup-', [status(thm)], ['119', '122'])).
% 3.74/4.01  thf('124', plain,
% 3.74/4.01      (![X0 : $i, X1 : $i]:
% 3.74/4.01         (((k1_relat_1 @ X0)
% 3.74/4.01            = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 3.74/4.01          | (zip_tseitin_0 @ X1 @ (k2_relat_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['123'])).
% 3.74/4.01  thf('125', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (((k1_relat_1 @ sk_C)
% 3.74/4.01            = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.74/4.01          | ~ (v1_relat_1 @ sk_C)
% 3.74/4.01          | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01          | (zip_tseitin_0 @ X0 @ (k2_relat_1 @ sk_C)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['111', '124'])).
% 3.74/4.01  thf('126', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.01  thf('127', plain,
% 3.74/4.01      (![X32 : $i]:
% 3.74/4.01         ((m1_subset_1 @ X32 @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 3.74/4.01          | ~ (v1_funct_1 @ X32)
% 3.74/4.01          | ~ (v1_relat_1 @ X32))),
% 3.74/4.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.74/4.01  thf('128', plain,
% 3.74/4.01      (((m1_subset_1 @ sk_C @ 
% 3.74/4.01         (k1_zfmisc_1 @ 
% 3.74/4.01          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 3.74/4.01        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup+', [status(thm)], ['126', '127'])).
% 3.74/4.01  thf('129', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf(cc1_relset_1, axiom,
% 3.74/4.01    (![A:$i,B:$i,C:$i]:
% 3.74/4.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.74/4.01       ( v1_relat_1 @ C ) ))).
% 3.74/4.01  thf('130', plain,
% 3.74/4.01      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.74/4.01         ((v1_relat_1 @ X4)
% 3.74/4.01          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 3.74/4.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.74/4.01  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('133', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['128', '131', '132'])).
% 3.74/4.01  thf('134', plain,
% 3.74/4.01      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.74/4.01         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 3.74/4.01            = (k1_relset_1 @ X14 @ X15 @ X16))
% 3.74/4.01          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.74/4.01      inference('cnf', [status(esa)], [t38_relset_1])).
% 3.74/4.01  thf('135', plain,
% 3.74/4.01      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 3.74/4.01         (k2_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['133', '134'])).
% 3.74/4.01  thf('136', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['128', '131', '132'])).
% 3.74/4.01  thf('137', plain,
% 3.74/4.01      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.74/4.01         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 3.74/4.01          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 3.74/4.01      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 3.74/4.01  thf('138', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ X0)
% 3.74/4.01           = (k10_relat_1 @ sk_C @ X0))),
% 3.74/4.01      inference('sup-', [status(thm)], ['136', '137'])).
% 3.74/4.01  thf('139', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('demod', [status(thm)], ['135', '138'])).
% 3.74/4.01  thf('140', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('142', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.01  thf('143', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))
% 3.74/4.01          | (zip_tseitin_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('demod', [status(thm)], ['125', '139', '140', '141', '142'])).
% 3.74/4.01  thf('144', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['52', '69'])).
% 3.74/4.01  thf('145', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01          | (zip_tseitin_0 @ X0 @ (k2_struct_0 @ sk_B))
% 3.74/4.01          | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['143', '144'])).
% 3.74/4.01  thf('146', plain,
% 3.74/4.01      (![X34 : $i]:
% 3.74/4.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 3.74/4.01          | ~ (l1_struct_0 @ X34)
% 3.74/4.01          | (v2_struct_0 @ X34))),
% 3.74/4.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.74/4.01  thf('147', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.74/4.01          | (zip_tseitin_0 @ X0 @ (k2_struct_0 @ sk_B))
% 3.74/4.01          | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01          | (v2_struct_0 @ sk_B)
% 3.74/4.01          | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup-', [status(thm)], ['145', '146'])).
% 3.74/4.01  thf('148', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.74/4.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.74/4.01  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('150', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((zip_tseitin_0 @ X0 @ (k2_struct_0 @ sk_B))
% 3.74/4.01          | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01          | (v2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['147', '148', '149'])).
% 3.74/4.01  thf('151', plain, (~ (v2_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('152', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01          | (zip_tseitin_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('clc', [status(thm)], ['150', '151'])).
% 3.74/4.01  thf('153', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('154', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['47', '48'])).
% 3.74/4.01  thf('155', plain,
% 3.74/4.01      (((m1_subset_1 @ sk_C @ 
% 3.74/4.01         (k1_zfmisc_1 @ 
% 3.74/4.01          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['153', '154'])).
% 3.74/4.01  thf('156', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('157', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['155', '156'])).
% 3.74/4.01  thf(t31_funct_2, axiom,
% 3.74/4.01    (![A:$i,B:$i,C:$i]:
% 3.74/4.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.74/4.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.74/4.01       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.74/4.01         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.74/4.01           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.74/4.01           ( m1_subset_1 @
% 3.74/4.01             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.74/4.01  thf('158', plain,
% 3.74/4.01      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X29)
% 3.74/4.01          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 3.74/4.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.74/4.01          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 3.74/4.01          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 3.74/4.01          | ~ (v1_funct_1 @ X29))),
% 3.74/4.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/4.01  thf('159', plain,
% 3.74/4.01      ((~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.74/4.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01            != (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['157', '158'])).
% 3.74/4.01  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('161', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('162', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['55', '56'])).
% 3.74/4.01  thf('163', plain,
% 3.74/4.01      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['161', '162'])).
% 3.74/4.01  thf('164', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('165', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['163', '164'])).
% 3.74/4.01  thf('166', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('167', plain,
% 3.74/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['91', '92'])).
% 3.74/4.01  thf('168', plain,
% 3.74/4.01      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01          = (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['166', '167'])).
% 3.74/4.01  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('170', plain,
% 3.74/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['168', '169'])).
% 3.74/4.01  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('172', plain,
% 3.74/4.01      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01         (k1_zfmisc_1 @ 
% 3.74/4.01          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.74/4.01        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('demod', [status(thm)], ['159', '160', '165', '170', '171'])).
% 3.74/4.01  thf('173', plain,
% 3.74/4.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/4.01      inference('simplify', [status(thm)], ['172'])).
% 3.74/4.01  thf('174', plain,
% 3.74/4.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.74/4.01         (~ (zip_tseitin_0 @ X22 @ X23)
% 3.74/4.01          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 3.74/4.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/4.01  thf('175', plain,
% 3.74/4.01      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01         (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['173', '174'])).
% 3.74/4.01  thf('176', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01           (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['152', '175'])).
% 3.74/4.01  thf('177', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['155', '156'])).
% 3.74/4.01  thf('178', plain,
% 3.74/4.01      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X29)
% 3.74/4.01          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 3.74/4.01          | (v1_funct_2 @ (k2_funct_1 @ X29) @ X30 @ X31)
% 3.74/4.01          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 3.74/4.01          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 3.74/4.01          | ~ (v1_funct_1 @ X29))),
% 3.74/4.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/4.01  thf('179', plain,
% 3.74/4.01      ((~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.01           (k2_struct_0 @ sk_A))
% 3.74/4.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01            != (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['177', '178'])).
% 3.74/4.01  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('181', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['163', '164'])).
% 3.74/4.01  thf('182', plain,
% 3.74/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['168', '169'])).
% 3.74/4.01  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('184', plain,
% 3.74/4.01      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.01         (k2_struct_0 @ sk_A))
% 3.74/4.01        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('demod', [status(thm)], ['179', '180', '181', '182', '183'])).
% 3.74/4.01  thf('185', plain,
% 3.74/4.01      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.01        (k2_struct_0 @ sk_A))),
% 3.74/4.01      inference('simplify', [status(thm)], ['184'])).
% 3.74/4.01  thf('186', plain,
% 3.74/4.01      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.74/4.01         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 3.74/4.01          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 3.74/4.01          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.74/4.01  thf('187', plain,
% 3.74/4.01      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01           (k2_struct_0 @ sk_B))
% 3.74/4.01        | ((k2_struct_0 @ sk_B)
% 3.74/4.01            = (k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01               (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['185', '186'])).
% 3.74/4.01  thf('188', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | ((k2_struct_0 @ sk_B)
% 3.74/4.01            = (k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01               (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['176', '187'])).
% 3.74/4.01  thf('189', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('190', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01          | (zip_tseitin_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('clc', [status(thm)], ['150', '151'])).
% 3.74/4.01  thf('191', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('192', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('193', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['47', '48'])).
% 3.74/4.01  thf('194', plain,
% 3.74/4.01      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X29)
% 3.74/4.01          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 3.74/4.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.74/4.01          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 3.74/4.01          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 3.74/4.01          | ~ (v1_funct_1 @ X29))),
% 3.74/4.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/4.01  thf('195', plain,
% 3.74/4.01      ((~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/4.01        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.74/4.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01            != (u1_struct_0 @ sk_B))
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['193', '194'])).
% 3.74/4.01  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('197', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['55', '56'])).
% 3.74/4.01  thf('198', plain,
% 3.74/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['91', '92'])).
% 3.74/4.01  thf('199', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('200', plain,
% 3.74/4.01      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01         (k1_zfmisc_1 @ 
% 3.74/4.01          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.74/4.01        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('demod', [status(thm)], ['195', '196', '197', '198', '199'])).
% 3.74/4.01  thf('201', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B)
% 3.74/4.01        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['192', '200'])).
% 3.74/4.01  thf('202', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('203', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/4.01        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 3.74/4.01      inference('demod', [status(thm)], ['201', '202'])).
% 3.74/4.01  thf('204', plain,
% 3.74/4.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 3.74/4.01      inference('simplify', [status(thm)], ['203'])).
% 3.74/4.01  thf('205', plain,
% 3.74/4.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.74/4.01         (~ (zip_tseitin_0 @ X22 @ X23)
% 3.74/4.01          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 3.74/4.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.74/4.01  thf('206', plain,
% 3.74/4.01      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01         (u1_struct_0 @ sk_B))
% 3.74/4.01        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['204', '205'])).
% 3.74/4.01  thf('207', plain,
% 3.74/4.01      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B)
% 3.74/4.01        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01           (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['191', '206'])).
% 3.74/4.01  thf('208', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('209', plain,
% 3.74/4.01      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01           (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('demod', [status(thm)], ['207', '208'])).
% 3.74/4.01  thf('210', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01           (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['190', '209'])).
% 3.74/4.01  thf('211', plain,
% 3.74/4.01      (![X33 : $i]:
% 3.74/4.01         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 3.74/4.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.74/4.01  thf('212', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['47', '48'])).
% 3.74/4.01  thf('213', plain,
% 3.74/4.01      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X29)
% 3.74/4.01          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 3.74/4.01          | (v1_funct_2 @ (k2_funct_1 @ X29) @ X30 @ X31)
% 3.74/4.01          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 3.74/4.01          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 3.74/4.01          | ~ (v1_funct_1 @ X29))),
% 3.74/4.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/4.01  thf('214', plain,
% 3.74/4.01      ((~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.74/4.01        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/4.01           (k2_struct_0 @ sk_A))
% 3.74/4.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01            != (u1_struct_0 @ sk_B))
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['212', '213'])).
% 3.74/4.01  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('216', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['55', '56'])).
% 3.74/4.01  thf('217', plain,
% 3.74/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['91', '92'])).
% 3.74/4.01  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('219', plain,
% 3.74/4.01      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/4.01         (k2_struct_0 @ sk_A))
% 3.74/4.01        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 3.74/4.01      inference('demod', [status(thm)], ['214', '215', '216', '217', '218'])).
% 3.74/4.01  thf('220', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B)
% 3.74/4.01        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/4.01           (k2_struct_0 @ sk_A)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['211', '219'])).
% 3.74/4.01  thf('221', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('222', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.74/4.01        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/4.01           (k2_struct_0 @ sk_A)))),
% 3.74/4.01      inference('demod', [status(thm)], ['220', '221'])).
% 3.74/4.01  thf('223', plain,
% 3.74/4.01      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.74/4.01        (k2_struct_0 @ sk_A))),
% 3.74/4.01      inference('simplify', [status(thm)], ['222'])).
% 3.74/4.01  thf('224', plain,
% 3.74/4.01      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.74/4.01         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 3.74/4.01          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 3.74/4.01          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.74/4.01  thf('225', plain,
% 3.74/4.01      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01           (u1_struct_0 @ sk_B))
% 3.74/4.01        | ((u1_struct_0 @ sk_B)
% 3.74/4.01            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01               (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['223', '224'])).
% 3.74/4.01  thf('226', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | ((u1_struct_0 @ sk_B)
% 3.74/4.01            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01               (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['210', '225'])).
% 3.74/4.01  thf('227', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B)
% 3.74/4.01          = (k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01             (k2_funct_1 @ sk_C)))
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B)
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['189', '226'])).
% 3.74/4.01  thf('228', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('229', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B)
% 3.74/4.01          = (k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.01             (k2_funct_1 @ sk_C)))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.74/4.01      inference('demod', [status(thm)], ['227', '228'])).
% 3.74/4.01  thf('230', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['188', '229'])).
% 3.74/4.01  thf('231', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | ((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('simplify', [status(thm)], ['230'])).
% 3.74/4.01  thf('232', plain,
% 3.74/4.01      (![X34 : $i]:
% 3.74/4.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 3.74/4.01          | ~ (l1_struct_0 @ X34)
% 3.74/4.01          | (v2_struct_0 @ X34))),
% 3.74/4.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.74/4.01  thf('233', plain,
% 3.74/4.01      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | (v2_struct_0 @ sk_B)
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup-', [status(thm)], ['231', '232'])).
% 3.74/4.01  thf('234', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('235', plain,
% 3.74/4.01      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | (v2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['233', '234'])).
% 3.74/4.01  thf('236', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.01  thf('237', plain,
% 3.74/4.01      (![X17 : $i, X18 : $i]:
% 3.74/4.01         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.74/4.01  thf('238', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.74/4.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.74/4.01  thf('239', plain,
% 3.74/4.01      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.74/4.01      inference('sup+', [status(thm)], ['237', '238'])).
% 3.74/4.01  thf('240', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['116', '117'])).
% 3.74/4.01  thf('241', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_xboole_0 @ (k2_relat_1 @ X0))
% 3.74/4.01          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('sup-', [status(thm)], ['239', '240'])).
% 3.74/4.01  thf('242', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.74/4.01          | ((k1_relat_1 @ X0)
% 3.74/4.01              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['120', '121'])).
% 3.74/4.01  thf('243', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | (v1_xboole_0 @ (k2_relat_1 @ X0))
% 3.74/4.01          | ((k1_relat_1 @ X0)
% 3.74/4.01              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('sup-', [status(thm)], ['241', '242'])).
% 3.74/4.01  thf('244', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (((k1_relat_1 @ X0)
% 3.74/4.01            = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 3.74/4.01          | (v1_xboole_0 @ (k2_relat_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['243'])).
% 3.74/4.01  thf('245', plain,
% 3.74/4.01      ((((k1_relat_1 @ sk_C)
% 3.74/4.01          = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.74/4.01        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['236', '244'])).
% 3.74/4.01  thf('246', plain,
% 3.74/4.01      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))
% 3.74/4.01         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 3.74/4.01      inference('demod', [status(thm)], ['135', '138'])).
% 3.74/4.01  thf('247', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('248', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('249', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.01  thf('250', plain,
% 3.74/4.01      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))
% 3.74/4.01        | (v1_xboole_0 @ (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('demod', [status(thm)], ['245', '246', '247', '248', '249'])).
% 3.74/4.01  thf('251', plain,
% 3.74/4.01      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['52', '69'])).
% 3.74/4.01  thf('252', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['250', '251'])).
% 3.74/4.01  thf('253', plain,
% 3.74/4.01      (![X34 : $i]:
% 3.74/4.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 3.74/4.01          | ~ (l1_struct_0 @ X34)
% 3.74/4.01          | (v2_struct_0 @ X34))),
% 3.74/4.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.74/4.01  thf('254', plain,
% 3.74/4.01      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.74/4.01        | (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | (v2_struct_0 @ sk_B)
% 3.74/4.01        | ~ (l1_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup-', [status(thm)], ['252', '253'])).
% 3.74/4.01  thf('255', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.74/4.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.74/4.01  thf('256', plain, ((l1_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('257', plain,
% 3.74/4.01      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | (v2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['254', '255', '256'])).
% 3.74/4.01  thf('258', plain, (~ (v2_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('259', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | (v1_xboole_0 @ (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('clc', [status(thm)], ['257', '258'])).
% 3.74/4.01  thf('260', plain,
% 3.74/4.01      (((v2_struct_0 @ sk_B) | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.74/4.01      inference('clc', [status(thm)], ['235', '259'])).
% 3.74/4.01  thf('261', plain, (~ (v2_struct_0 @ sk_B)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('262', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.74/4.01      inference('clc', [status(thm)], ['260', '261'])).
% 3.74/4.01  thf('263', plain,
% 3.74/4.01      (![X3 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X3)
% 3.74/4.01          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 3.74/4.01          | ~ (v1_funct_1 @ X3)
% 3.74/4.01          | ~ (v1_relat_1 @ X3))),
% 3.74/4.01      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.74/4.01  thf('264', plain,
% 3.74/4.01      (![X2 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X2)
% 3.74/4.01          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 3.74/4.01          | ~ (v1_funct_1 @ X2)
% 3.74/4.01          | ~ (v1_relat_1 @ X2))),
% 3.74/4.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.74/4.01  thf('265', plain,
% 3.74/4.01      (![X1 : $i]:
% 3.74/4.01         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 3.74/4.01          | ~ (v2_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_relat_1 @ X1))),
% 3.74/4.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/4.01  thf(dt_k2_funct_1, axiom,
% 3.74/4.01    (![A:$i]:
% 3.74/4.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.74/4.01       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.74/4.01         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.74/4.01  thf('266', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.74/4.01  thf('267', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.74/4.01  thf('268', plain,
% 3.74/4.01      (![X3 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X3)
% 3.74/4.01          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 3.74/4.01          | ~ (v1_funct_1 @ X3)
% 3.74/4.01          | ~ (v1_relat_1 @ X3))),
% 3.74/4.01      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.74/4.01  thf('269', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.74/4.01  thf('270', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.74/4.01  thf('271', plain,
% 3.74/4.01      (![X2 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X2)
% 3.74/4.01          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 3.74/4.01          | ~ (v1_funct_1 @ X2)
% 3.74/4.01          | ~ (v1_relat_1 @ X2))),
% 3.74/4.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.74/4.01  thf('272', plain,
% 3.74/4.01      (![X32 : $i]:
% 3.74/4.01         ((m1_subset_1 @ X32 @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 3.74/4.01          | ~ (v1_funct_1 @ X32)
% 3.74/4.01          | ~ (v1_relat_1 @ X32))),
% 3.74/4.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.74/4.01  thf('273', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['271', '272'])).
% 3.74/4.01  thf('274', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 3.74/4.01               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['270', '273'])).
% 3.74/4.01  thf('275', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['274'])).
% 3.74/4.01  thf('276', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 3.74/4.01               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['269', '275'])).
% 3.74/4.01  thf('277', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['276'])).
% 3.74/4.01  thf('278', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['268', '277'])).
% 3.74/4.01  thf('279', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01               (k2_relat_1 @ X0)))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['267', '278'])).
% 3.74/4.01  thf('280', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['279'])).
% 3.74/4.01  thf('281', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01               (k2_relat_1 @ X0)))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['266', '280'])).
% 3.74/4.01  thf('282', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['281'])).
% 3.74/4.01  thf('283', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01               (k2_relat_1 @ X0)))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['265', '282'])).
% 3.74/4.01  thf('284', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['283'])).
% 3.74/4.01  thf('285', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0))),
% 3.74/4.01      inference('sup+', [status(thm)], ['264', '284'])).
% 3.74/4.01  thf('286', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 3.74/4.01      inference('simplify', [status(thm)], ['285'])).
% 3.74/4.01  thf('287', plain,
% 3.74/4.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.74/4.01         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 3.74/4.01          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.74/4.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.74/4.01  thf('288', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.74/4.01              (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.74/4.01              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['286', '287'])).
% 3.74/4.01  thf('289', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.01            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('sup+', [status(thm)], ['263', '288'])).
% 3.74/4.01  thf('290', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.01              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.74/4.01      inference('simplify', [status(thm)], ['289'])).
% 3.74/4.01  thf('291', plain,
% 3.74/4.01      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.74/4.01          = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.74/4.01        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup+', [status(thm)], ['262', '290'])).
% 3.74/4.01  thf('292', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.01  thf('293', plain,
% 3.74/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['168', '169'])).
% 3.74/4.01  thf('294', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('295', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('296', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('297', plain,
% 3.74/4.01      (((k2_struct_0 @ sk_B)
% 3.74/4.01         = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('demod', [status(thm)],
% 3.74/4.01                ['291', '292', '293', '294', '295', '296'])).
% 3.74/4.01  thf('298', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.74/4.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['106', '297'])).
% 3.74/4.01  thf('299', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.01  thf('300', plain,
% 3.74/4.01      (![X2 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X2)
% 3.74/4.01          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 3.74/4.01          | ~ (v1_funct_1 @ X2)
% 3.74/4.01          | ~ (v1_relat_1 @ X2))),
% 3.74/4.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.74/4.01  thf('301', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['276'])).
% 3.74/4.01  thf('302', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0))),
% 3.74/4.01      inference('sup+', [status(thm)], ['300', '301'])).
% 3.74/4.01  thf('303', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 3.74/4.01      inference('simplify', [status(thm)], ['302'])).
% 3.74/4.01  thf('304', plain,
% 3.74/4.01      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01         (k1_zfmisc_1 @ 
% 3.74/4.01          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 3.74/4.01        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup+', [status(thm)], ['299', '303'])).
% 3.74/4.01  thf('305', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('306', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('307', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('308', plain,
% 3.74/4.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.74/4.01      inference('demod', [status(thm)], ['304', '305', '306', '307'])).
% 3.74/4.01  thf('309', plain,
% 3.74/4.01      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.74/4.01         ((v1_relat_1 @ X4)
% 3.74/4.01          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 3.74/4.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.74/4.01  thf('310', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['308', '309'])).
% 3.74/4.01  thf('311', plain,
% 3.74/4.01      ((m1_subset_1 @ sk_C @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['155', '156'])).
% 3.74/4.01  thf('312', plain,
% 3.74/4.01      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X29)
% 3.74/4.01          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 3.74/4.01          | (v1_funct_1 @ (k2_funct_1 @ X29))
% 3.74/4.01          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 3.74/4.01          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 3.74/4.01          | ~ (v1_funct_1 @ X29))),
% 3.74/4.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/4.01  thf('313', plain,
% 3.74/4.01      ((~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/4.01        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01            != (k2_struct_0 @ sk_B))
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['311', '312'])).
% 3.74/4.01  thf('314', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('315', plain,
% 3.74/4.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['163', '164'])).
% 3.74/4.01  thf('316', plain,
% 3.74/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.74/4.01         = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('demod', [status(thm)], ['168', '169'])).
% 3.74/4.01  thf('317', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('318', plain,
% 3.74/4.01      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.74/4.01      inference('demod', [status(thm)], ['313', '314', '315', '316', '317'])).
% 3.74/4.01  thf('319', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.74/4.01      inference('simplify', [status(thm)], ['318'])).
% 3.74/4.01  thf('320', plain,
% 3.74/4.01      ((((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.74/4.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('demod', [status(thm)], ['298', '310', '319'])).
% 3.74/4.01  thf('321', plain,
% 3.74/4.01      ((~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C)
% 3.74/4.01        | ((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['105', '320'])).
% 3.74/4.01  thf('322', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('323', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('324', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('325', plain,
% 3.74/4.01      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('demod', [status(thm)], ['321', '322', '323', '324'])).
% 3.74/4.01  thf('326', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.01              = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.74/4.01      inference('simplify', [status(thm)], ['289'])).
% 3.74/4.01  thf('327', plain,
% 3.74/4.01      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.01          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 3.74/4.01          = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 3.74/4.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['325', '326'])).
% 3.74/4.01  thf('328', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.01  thf('329', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['276'])).
% 3.74/4.01  thf('330', plain,
% 3.74/4.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.74/4.01         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 3.74/4.01          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.74/4.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.74/4.01  thf('331', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ 
% 3.74/4.01              (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 3.74/4.01              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['329', '330'])).
% 3.74/4.01  thf('332', plain,
% 3.74/4.01      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.01          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 3.74/4.01          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v1_relat_1 @ sk_C))),
% 3.74/4.01      inference('sup+', [status(thm)], ['328', '331'])).
% 3.74/4.01  thf('333', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('334', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('335', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('336', plain,
% 3.74/4.01      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.01         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 3.74/4.01         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('demod', [status(thm)], ['332', '333', '334', '335'])).
% 3.74/4.01  thf('337', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup-', [status(thm)], ['308', '309'])).
% 3.74/4.01  thf('338', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.74/4.01      inference('simplify', [status(thm)], ['318'])).
% 3.74/4.01  thf('339', plain,
% 3.74/4.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01          = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 3.74/4.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('demod', [status(thm)], ['327', '336', '337', '338'])).
% 3.74/4.01  thf('340', plain,
% 3.74/4.01      ((~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C)
% 3.74/4.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01            = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['104', '339'])).
% 3.74/4.01  thf('341', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('342', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('343', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('344', plain,
% 3.74/4.01      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01         = (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 3.74/4.01      inference('demod', [status(thm)], ['340', '341', '342', '343'])).
% 3.74/4.01  thf('345', plain,
% 3.74/4.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01          = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.74/4.01        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/4.01        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/4.01        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('sup+', [status(thm)], ['103', '344'])).
% 3.74/4.01  thf('346', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.74/4.01      inference('clc', [status(thm)], ['260', '261'])).
% 3.74/4.01  thf('347', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 3.74/4.01      inference('simplify', [status(thm)], ['285'])).
% 3.74/4.01  thf('348', plain,
% 3.74/4.01      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/4.01         (k1_zfmisc_1 @ 
% 3.74/4.01          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))
% 3.74/4.01        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup+', [status(thm)], ['346', '347'])).
% 3.74/4.01  thf('349', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.01      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.01  thf('350', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('351', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('352', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('353', plain,
% 3.74/4.01      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/4.01        (k1_zfmisc_1 @ 
% 3.74/4.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/4.01      inference('demod', [status(thm)], ['348', '349', '350', '351', '352'])).
% 3.74/4.01  thf('354', plain,
% 3.74/4.01      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.74/4.01         ((v1_relat_1 @ X4)
% 3.74/4.01          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 3.74/4.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.74/4.01  thf('355', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['353', '354'])).
% 3.74/4.01  thf('356', plain,
% 3.74/4.01      (![X2 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X2)
% 3.74/4.01          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 3.74/4.01          | ~ (v1_funct_1 @ X2)
% 3.74/4.01          | ~ (v1_relat_1 @ X2))),
% 3.74/4.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.74/4.01  thf('357', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.74/4.01      inference('simplify', [status(thm)], ['318'])).
% 3.74/4.01  thf('358', plain,
% 3.74/4.01      (![X1 : $i]:
% 3.74/4.01         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 3.74/4.01          | ~ (v2_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_funct_1 @ X1)
% 3.74/4.01          | ~ (v1_relat_1 @ X1))),
% 3.74/4.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/4.01  thf('359', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 3.74/4.01      inference('simplify', [status(thm)], ['302'])).
% 3.74/4.01  thf('360', plain,
% 3.74/4.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.74/4.01         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 3.74/4.01          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.74/4.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.74/4.01  thf('361', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 3.74/4.01              (k2_funct_1 @ X0)) = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['359', '360'])).
% 3.74/4.01  thf('362', plain,
% 3.74/4.01      (![X2 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X2)
% 3.74/4.01          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 3.74/4.01          | ~ (v1_funct_1 @ X2)
% 3.74/4.01          | ~ (v1_relat_1 @ X2))),
% 3.74/4.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.74/4.01  thf('363', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.74/4.01  thf('364', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.74/4.01  thf('365', plain,
% 3.74/4.01      (![X2 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X2)
% 3.74/4.01          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 3.74/4.01          | ~ (v1_funct_1 @ X2)
% 3.74/4.01          | ~ (v1_relat_1 @ X2))),
% 3.74/4.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.74/4.01  thf('366', plain,
% 3.74/4.01      (![X32 : $i]:
% 3.74/4.01         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 3.74/4.01          | ~ (v1_funct_1 @ X32)
% 3.74/4.01          | ~ (v1_relat_1 @ X32))),
% 3.74/4.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.74/4.01  thf('367', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01           (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 3.74/4.01      inference('sup+', [status(thm)], ['365', '366'])).
% 3.74/4.01  thf('368', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['364', '367'])).
% 3.74/4.01  thf('369', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01           (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['368'])).
% 3.74/4.01  thf('370', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['363', '369'])).
% 3.74/4.01  thf('371', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.01           (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['370'])).
% 3.74/4.01  thf('372', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.74/4.01           (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0))),
% 3.74/4.01      inference('sup+', [status(thm)], ['362', '371'])).
% 3.74/4.01  thf('373', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.74/4.01             (k1_relat_1 @ X0)))),
% 3.74/4.01      inference('simplify', [status(thm)], ['372'])).
% 3.74/4.01  thf('374', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 3.74/4.01             (k1_zfmisc_1 @ 
% 3.74/4.01              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 3.74/4.01      inference('simplify', [status(thm)], ['302'])).
% 3.74/4.01  thf('375', plain,
% 3.74/4.01      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.74/4.01         (~ (v2_funct_1 @ X29)
% 3.74/4.01          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 3.74/4.01          | (v1_funct_1 @ (k2_funct_1 @ X29))
% 3.74/4.01          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 3.74/4.01          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 3.74/4.01          | ~ (v1_funct_1 @ X29))),
% 3.74/4.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.74/4.01  thf('376', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 3.74/4.01               (k1_relat_1 @ X0))
% 3.74/4.01          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.74/4.01          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 3.74/4.01              (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['374', '375'])).
% 3.74/4.01  thf('377', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 3.74/4.01              (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.74/4.01          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('sup-', [status(thm)], ['373', '376'])).
% 3.74/4.01  thf('378', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.74/4.01          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 3.74/4.01              (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['377'])).
% 3.74/4.01  thf('379', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['361', '378'])).
% 3.74/4.01  thf('380', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.74/4.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0)))),
% 3.74/4.01      inference('simplify', [status(thm)], ['379'])).
% 3.74/4.01  thf('381', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0)
% 3.74/4.01          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.74/4.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['358', '380'])).
% 3.74/4.01  thf('382', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.01          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.74/4.01          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.74/4.01          | ~ (v2_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_relat_1 @ X0))),
% 3.74/4.01      inference('simplify', [status(thm)], ['381'])).
% 3.74/4.01  thf('383', plain,
% 3.74/4.01      ((~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C)
% 3.74/4.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.74/4.01        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['357', '382'])).
% 3.74/4.01  thf('384', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('385', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('386', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('387', plain,
% 3.74/4.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.74/4.01        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('demod', [status(thm)], ['383', '384', '385', '386'])).
% 3.74/4.01  thf('388', plain,
% 3.74/4.01      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.74/4.01        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C)
% 3.74/4.01        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['356', '387'])).
% 3.74/4.01  thf('389', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('390', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('391', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('392', plain,
% 3.74/4.01      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.74/4.01        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('demod', [status(thm)], ['388', '389', '390', '391'])).
% 3.74/4.01  thf('393', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.01      inference('simplify', [status(thm)], ['392'])).
% 3.74/4.01  thf('394', plain,
% 3.74/4.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01          = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.74/4.01        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('demod', [status(thm)], ['345', '355', '393'])).
% 3.74/4.01  thf('395', plain,
% 3.74/4.01      ((~ (v2_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C)
% 3.74/4.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 3.74/4.01      inference('sup-', [status(thm)], ['102', '394'])).
% 3.74/4.01  thf('396', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('397', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('398', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('399', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('400', plain,
% 3.74/4.01      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.01         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.01      inference('demod', [status(thm)], ['395', '396', '397', '398', '399'])).
% 3.74/4.01  thf('401', plain,
% 3.74/4.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 3.74/4.01        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.01        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.01        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.01      inference('sup+', [status(thm)], ['101', '400'])).
% 3.74/4.01  thf('402', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.74/4.01      inference('clc', [status(thm)], ['260', '261'])).
% 3.74/4.01  thf('403', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.01      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.01  thf('404', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('405', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.01  thf('406', plain,
% 3.74/4.01      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.74/4.01      inference('demod', [status(thm)], ['401', '402', '403', '404', '405'])).
% 3.74/4.01  thf('407', plain,
% 3.74/4.01      (![X32 : $i]:
% 3.74/4.01         ((m1_subset_1 @ X32 @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 3.74/4.01          | ~ (v1_funct_1 @ X32)
% 3.74/4.01          | ~ (v1_relat_1 @ X32))),
% 3.74/4.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.74/4.01  thf('408', plain,
% 3.74/4.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.74/4.01         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 3.74/4.01          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.74/4.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.74/4.01  thf('409', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.01              = (k2_relat_1 @ X0)))),
% 3.74/4.01      inference('sup-', [status(thm)], ['407', '408'])).
% 3.74/4.01  thf('410', plain,
% 3.74/4.01      (![X32 : $i]:
% 3.74/4.01         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 3.74/4.01          | ~ (v1_funct_1 @ X32)
% 3.74/4.01          | ~ (v1_relat_1 @ X32))),
% 3.74/4.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.74/4.01  thf('411', plain,
% 3.74/4.01      (![X32 : $i]:
% 3.74/4.01         ((m1_subset_1 @ X32 @ 
% 3.74/4.01           (k1_zfmisc_1 @ 
% 3.74/4.01            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 3.74/4.01          | ~ (v1_funct_1 @ X32)
% 3.74/4.01          | ~ (v1_relat_1 @ X32))),
% 3.74/4.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.74/4.01  thf('412', plain,
% 3.74/4.01      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.74/4.01         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 3.74/4.01          | ~ (v2_funct_1 @ X37)
% 3.74/4.01          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 3.74/4.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 3.74/4.01          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 3.74/4.01          | ~ (v1_funct_1 @ X37))),
% 3.74/4.01      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.74/4.01  thf('413', plain,
% 3.74/4.01      (![X0 : $i]:
% 3.74/4.01         (~ (v1_relat_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_1 @ X0)
% 3.74/4.01          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 3.74/4.01          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02              = (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02              != (k2_relat_1 @ X0)))),
% 3.74/4.02      inference('sup-', [status(thm)], ['411', '412'])).
% 3.74/4.02  thf('414', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02            != (k2_relat_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02              = (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0))),
% 3.74/4.02      inference('simplify', [status(thm)], ['413'])).
% 3.74/4.02  thf('415', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         (~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02              = (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02              != (k2_relat_1 @ X0)))),
% 3.74/4.02      inference('sup-', [status(thm)], ['410', '414'])).
% 3.74/4.02  thf('416', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02            != (k2_relat_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02              = (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0))),
% 3.74/4.02      inference('simplify', [status(thm)], ['415'])).
% 3.74/4.02  thf('417', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02              = (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ X0))),
% 3.74/4.02      inference('sup-', [status(thm)], ['409', '416'])).
% 3.74/4.02  thf('418', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         (~ (v2_funct_1 @ X0)
% 3.74/4.02          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.74/4.02              = (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0))),
% 3.74/4.02      inference('simplify', [status(thm)], ['417'])).
% 3.74/4.02  thf('419', plain,
% 3.74/4.02      ((((k2_tops_2 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/4.02          (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C))
% 3.74/4.02          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/4.02        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.02        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.74/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.02      inference('sup+', [status(thm)], ['406', '418'])).
% 3.74/4.02  thf('420', plain,
% 3.74/4.02      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.02      inference('demod', [status(thm)], ['321', '322', '323', '324'])).
% 3.74/4.02  thf('421', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.74/4.02      inference('simplify', [status(thm)], ['318'])).
% 3.74/4.02  thf('422', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.74/4.02      inference('sup-', [status(thm)], ['308', '309'])).
% 3.74/4.02  thf('423', plain,
% 3.74/4.02      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.02          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/4.02        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.02      inference('demod', [status(thm)], ['419', '420', '421', '422'])).
% 3.74/4.02  thf('424', plain,
% 3.74/4.02      ((~ (v1_relat_1 @ sk_C)
% 3.74/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.02        | ~ (v2_funct_1 @ sk_C)
% 3.74/4.02        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.02            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.02      inference('sup-', [status(thm)], ['100', '423'])).
% 3.74/4.02  thf('425', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.02      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.02  thf('426', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.02  thf('427', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.02  thf('428', plain,
% 3.74/4.02      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.74/4.02         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.02      inference('demod', [status(thm)], ['424', '425', '426', '427'])).
% 3.74/4.02  thf('429', plain,
% 3.74/4.02      (![X3 : $i]:
% 3.74/4.02         (~ (v2_funct_1 @ X3)
% 3.74/4.02          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 3.74/4.02          | ~ (v1_funct_1 @ X3)
% 3.74/4.02          | ~ (v1_relat_1 @ X3))),
% 3.74/4.02      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.74/4.02  thf('430', plain,
% 3.74/4.02      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/4.02        (k1_zfmisc_1 @ 
% 3.74/4.02         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.74/4.02      inference('demod', [status(thm)], ['348', '349', '350', '351', '352'])).
% 3.74/4.02  thf(redefinition_r2_funct_2, axiom,
% 3.74/4.02    (![A:$i,B:$i,C:$i,D:$i]:
% 3.74/4.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.74/4.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.74/4.02         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.74/4.02         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.74/4.02       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.74/4.02  thf('431', plain,
% 3.74/4.02      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.74/4.02         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.74/4.02          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 3.74/4.02          | ~ (v1_funct_1 @ X25)
% 3.74/4.02          | ~ (v1_funct_1 @ X28)
% 3.74/4.02          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 3.74/4.02          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.74/4.02          | (r2_funct_2 @ X26 @ X27 @ X25 @ X28)
% 3.74/4.02          | ((X25) != (X28)))),
% 3.74/4.02      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 3.74/4.02  thf('432', plain,
% 3.74/4.02      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.74/4.02         ((r2_funct_2 @ X26 @ X27 @ X28 @ X28)
% 3.74/4.02          | ~ (v1_funct_1 @ X28)
% 3.74/4.02          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 3.74/4.02          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.74/4.02      inference('simplify', [status(thm)], ['431'])).
% 3.74/4.02  thf('433', plain,
% 3.74/4.02      ((~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/4.02           (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.74/4.02        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.74/4.02        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.02           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/4.02           (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.74/4.02      inference('sup-', [status(thm)], ['430', '432'])).
% 3.74/4.02  thf('434', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.74/4.02      inference('sup+', [status(thm)], ['109', '110'])).
% 3.74/4.02  thf('435', plain,
% 3.74/4.02      (![X2 : $i]:
% 3.74/4.02         (~ (v2_funct_1 @ X2)
% 3.74/4.02          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 3.74/4.02          | ~ (v1_funct_1 @ X2)
% 3.74/4.02          | ~ (v1_relat_1 @ X2))),
% 3.74/4.02      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.74/4.02  thf('436', plain,
% 3.74/4.02      (![X1 : $i]:
% 3.74/4.02         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 3.74/4.02          | ~ (v2_funct_1 @ X1)
% 3.74/4.02          | ~ (v1_funct_1 @ X1)
% 3.74/4.02          | ~ (v1_relat_1 @ X1))),
% 3.74/4.02      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.74/4.02  thf('437', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0))),
% 3.74/4.02      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.74/4.02  thf('438', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0))),
% 3.74/4.02      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.74/4.02  thf('439', plain,
% 3.74/4.02      (![X3 : $i]:
% 3.74/4.02         (~ (v2_funct_1 @ X3)
% 3.74/4.02          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 3.74/4.02          | ~ (v1_funct_1 @ X3)
% 3.74/4.02          | ~ (v1_relat_1 @ X3))),
% 3.74/4.02      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.74/4.02  thf('440', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.02           (k1_relat_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0))),
% 3.74/4.02      inference('simplify', [status(thm)], ['370'])).
% 3.74/4.02  thf('441', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 3.74/4.02           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.74/4.02      inference('sup+', [status(thm)], ['439', '440'])).
% 3.74/4.02  thf('442', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         (~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.02             (k1_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 3.74/4.02      inference('sup-', [status(thm)], ['438', '441'])).
% 3.74/4.02  thf('443', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 3.74/4.02           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0))),
% 3.74/4.02      inference('simplify', [status(thm)], ['442'])).
% 3.74/4.02  thf('444', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         (~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.02             (k1_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 3.74/4.02      inference('sup-', [status(thm)], ['437', '443'])).
% 3.74/4.02  thf('445', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 3.74/4.02           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0))),
% 3.74/4.02      inference('simplify', [status(thm)], ['444'])).
% 3.74/4.02  thf('446', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         (~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.02             (k1_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 3.74/4.02      inference('sup-', [status(thm)], ['436', '445'])).
% 3.74/4.02  thf('447', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 3.74/4.02           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0))),
% 3.74/4.02      inference('simplify', [status(thm)], ['446'])).
% 3.74/4.02  thf('448', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0) @ 
% 3.74/4.02           (k2_relat_1 @ X0))
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v2_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v2_funct_1 @ X0))),
% 3.74/4.02      inference('sup+', [status(thm)], ['435', '447'])).
% 3.74/4.02  thf('449', plain,
% 3.74/4.02      (![X0 : $i]:
% 3.74/4.02         (~ (v2_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_funct_1 @ X0)
% 3.74/4.02          | ~ (v1_relat_1 @ X0)
% 3.74/4.02          | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.74/4.02             (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.74/4.02      inference('simplify', [status(thm)], ['448'])).
% 3.74/4.02  thf('450', plain,
% 3.74/4.02      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/4.02         (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.74/4.02        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.02        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.02      inference('sup+', [status(thm)], ['434', '449'])).
% 3.74/4.02  thf('451', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.02      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.02  thf('452', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.02  thf('453', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.02  thf('454', plain,
% 3.74/4.02      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/4.02        (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 3.74/4.02      inference('demod', [status(thm)], ['450', '451', '452', '453'])).
% 3.74/4.02  thf('455', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.74/4.02      inference('clc', [status(thm)], ['260', '261'])).
% 3.74/4.02  thf('456', plain,
% 3.74/4.02      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.74/4.02        (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.74/4.02      inference('demod', [status(thm)], ['454', '455'])).
% 3.74/4.02  thf('457', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.02      inference('simplify', [status(thm)], ['392'])).
% 3.74/4.02  thf('458', plain,
% 3.74/4.02      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.02        (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.74/4.02      inference('demod', [status(thm)], ['433', '456', '457'])).
% 3.74/4.02  thf('459', plain,
% 3.74/4.02      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.02         (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 3.74/4.02        | ~ (v1_relat_1 @ sk_C)
% 3.74/4.02        | ~ (v1_funct_1 @ sk_C)
% 3.74/4.02        | ~ (v2_funct_1 @ sk_C))),
% 3.74/4.02      inference('sup+', [status(thm)], ['429', '458'])).
% 3.74/4.02  thf('460', plain, ((v1_relat_1 @ sk_C)),
% 3.74/4.02      inference('sup-', [status(thm)], ['129', '130'])).
% 3.74/4.02  thf('461', plain, ((v1_funct_1 @ sk_C)),
% 3.74/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.02  thf('462', plain, ((v2_funct_1 @ sk_C)),
% 3.74/4.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.74/4.02  thf('463', plain,
% 3.74/4.02      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 3.74/4.02        (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 3.74/4.02      inference('demod', [status(thm)], ['459', '460', '461', '462'])).
% 3.74/4.02  thf('464', plain, ($false),
% 3.74/4.02      inference('demod', [status(thm)], ['99', '428', '463'])).
% 3.74/4.02  
% 3.74/4.02  % SZS output end Refutation
% 3.74/4.02  
% 3.87/4.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
