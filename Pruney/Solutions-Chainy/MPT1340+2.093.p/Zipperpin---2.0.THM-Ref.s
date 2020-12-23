%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QiVkp1G1Uk

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:23 EST 2020

% Result     : Theorem 4.69s
% Output     : Refutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  330 (9457 expanded)
%              Number of leaves         :   45 (2753 expanded)
%              Depth                    :   35
%              Number of atoms          : 3177 (207377 expanded)
%              Number of equality atoms :  178 (7081 expanded)
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['9','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','30','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('43',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

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

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('61',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','57','58','61'])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','40','41','42','47','67'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('69',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('70',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

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

thf('79',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('99',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['91','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','90','104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
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

thf('109',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('111',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('120',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('121',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('124',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('129',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('130',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','118','127','130'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('132',plain,(
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

thf('133',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('134',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('135',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

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
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('141',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['135','143'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('146',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('150',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['117'])).

thf('152',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('154',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('158',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156','157','158','159'])).

thf('161',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','160'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('163',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151','165'])).

thf('167',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('168',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('169',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['166','169'])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['134','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('175',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['171','176','177','178'])).

thf('180',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['133','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

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

thf('187',plain,(
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

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['185','191'])).

thf('193',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('194',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('195',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('196',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('197',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['117'])).

thf('199',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['164'])).

thf('200',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('202',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['194','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['203','204','205','206'])).

thf('208',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['193','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['208','209','210','211'])).

thf('213',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('215',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('216',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('217',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('218',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['117'])).

thf('220',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['164'])).

thf('221',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('223',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['215','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','228'])).

thf('230',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('231',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230','231','232'])).

thf('234',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['233'])).

thf('235',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['192','213','234'])).

thf('236',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['132','235'])).

thf('237',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('238',plain,(
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

thf('239',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_funct_2 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['237','239'])).

thf('241',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('245',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','243','244','245','246'])).

thf('248',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('249',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','243','244','245','246'])).

thf('250',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('251',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('252',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('253',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('254',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['253','254'])).

thf('256',plain,(
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
    inference('sup-',[status(thm)],['252','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,(
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
    inference('sup-',[status(thm)],['251','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['250','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['249','261'])).

thf('263',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('265',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('267',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['117'])).

thf('269',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['262','267','268'])).

thf('270',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['248','269'])).

thf('271',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('272',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['270','271','272','273'])).

thf('275',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','247','274'])).

thf('276',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['69','276'])).

thf('278',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('279',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['277','278','279','280'])).

thf('282',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('283',plain,(
    $false ),
    inference(demod,[status(thm)],['68','281','282'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QiVkp1G1Uk
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:52:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.69/4.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.69/4.87  % Solved by: fo/fo7.sh
% 4.69/4.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.69/4.87  % done 1182 iterations in 4.397s
% 4.69/4.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.69/4.87  % SZS output start Refutation
% 4.69/4.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.69/4.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.69/4.87  thf(sk_A_type, type, sk_A: $i).
% 4.69/4.87  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.69/4.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.69/4.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.69/4.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.69/4.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.69/4.87  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.69/4.87  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.69/4.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.69/4.87  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.69/4.87  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.69/4.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.69/4.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.69/4.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.69/4.87  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.69/4.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.69/4.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.69/4.87  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.69/4.87  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 4.69/4.87  thf(sk_B_type, type, sk_B: $i).
% 4.69/4.87  thf(sk_C_type, type, sk_C: $i).
% 4.69/4.87  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 4.69/4.87  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.69/4.87  thf(d3_struct_0, axiom,
% 4.69/4.87    (![A:$i]:
% 4.69/4.87     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.69/4.87  thf('0', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf('1', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf(t64_tops_2, conjecture,
% 4.69/4.87    (![A:$i]:
% 4.69/4.87     ( ( l1_struct_0 @ A ) =>
% 4.69/4.87       ( ![B:$i]:
% 4.69/4.87         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 4.69/4.87           ( ![C:$i]:
% 4.69/4.87             ( ( ( v1_funct_1 @ C ) & 
% 4.69/4.87                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.69/4.87                 ( m1_subset_1 @
% 4.69/4.87                   C @ 
% 4.69/4.87                   ( k1_zfmisc_1 @
% 4.69/4.87                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.69/4.87               ( ( ( ( k2_relset_1 @
% 4.69/4.87                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.69/4.87                     ( k2_struct_0 @ B ) ) & 
% 4.69/4.87                   ( v2_funct_1 @ C ) ) =>
% 4.69/4.87                 ( r2_funct_2 @
% 4.69/4.87                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 4.69/4.87                   ( k2_tops_2 @
% 4.69/4.87                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.69/4.87                     ( k2_tops_2 @
% 4.69/4.87                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 4.69/4.87                   C ) ) ) ) ) ) ))).
% 4.69/4.87  thf(zf_stmt_0, negated_conjecture,
% 4.69/4.87    (~( ![A:$i]:
% 4.69/4.87        ( ( l1_struct_0 @ A ) =>
% 4.69/4.87          ( ![B:$i]:
% 4.69/4.87            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 4.69/4.87              ( ![C:$i]:
% 4.69/4.87                ( ( ( v1_funct_1 @ C ) & 
% 4.69/4.87                    ( v1_funct_2 @
% 4.69/4.87                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.69/4.87                    ( m1_subset_1 @
% 4.69/4.87                      C @ 
% 4.69/4.87                      ( k1_zfmisc_1 @
% 4.69/4.87                        ( k2_zfmisc_1 @
% 4.69/4.87                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.69/4.87                  ( ( ( ( k2_relset_1 @
% 4.69/4.87                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.69/4.87                        ( k2_struct_0 @ B ) ) & 
% 4.69/4.87                      ( v2_funct_1 @ C ) ) =>
% 4.69/4.87                    ( r2_funct_2 @
% 4.69/4.87                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 4.69/4.87                      ( k2_tops_2 @
% 4.69/4.87                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.69/4.87                        ( k2_tops_2 @
% 4.69/4.87                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 4.69/4.87                      C ) ) ) ) ) ) ) )),
% 4.69/4.87    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 4.69/4.87  thf('2', plain,
% 4.69/4.87      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.69/4.87           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 4.69/4.87          sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('3', plain,
% 4.69/4.87      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.69/4.87            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 4.69/4.87           sk_C)
% 4.69/4.87        | ~ (l1_struct_0 @ sk_A))),
% 4.69/4.87      inference('sup-', [status(thm)], ['1', '2'])).
% 4.69/4.87  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('5', plain,
% 4.69/4.87      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.69/4.87           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 4.69/4.87          sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['3', '4'])).
% 4.69/4.87  thf('6', plain,
% 4.69/4.87      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.69/4.87            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 4.69/4.87           sk_C)
% 4.69/4.87        | ~ (l1_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup-', [status(thm)], ['0', '5'])).
% 4.69/4.87  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('8', plain,
% 4.69/4.87      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.69/4.87           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 4.69/4.87          sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['6', '7'])).
% 4.69/4.87  thf('9', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf(d1_funct_2, axiom,
% 4.69/4.87    (![A:$i,B:$i,C:$i]:
% 4.69/4.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.69/4.87       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.69/4.87           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.69/4.87             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.69/4.87         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.69/4.87           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.69/4.87             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.69/4.87  thf(zf_stmt_1, axiom,
% 4.69/4.87    (![B:$i,A:$i]:
% 4.69/4.87     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.69/4.87       ( zip_tseitin_0 @ B @ A ) ))).
% 4.69/4.87  thf('10', plain,
% 4.69/4.87      (![X13 : $i, X14 : $i]:
% 4.69/4.87         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.69/4.87  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.69/4.87  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.69/4.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.69/4.87  thf('12', plain,
% 4.69/4.87      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.69/4.87      inference('sup+', [status(thm)], ['10', '11'])).
% 4.69/4.87  thf('13', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.69/4.87  thf(zf_stmt_3, axiom,
% 4.69/4.87    (![C:$i,B:$i,A:$i]:
% 4.69/4.87     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.69/4.87       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.69/4.87  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.69/4.87  thf(zf_stmt_5, axiom,
% 4.69/4.87    (![A:$i,B:$i,C:$i]:
% 4.69/4.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.69/4.87       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.69/4.87         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.69/4.87           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.69/4.87             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.69/4.87  thf('14', plain,
% 4.69/4.87      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.69/4.87         (~ (zip_tseitin_0 @ X18 @ X19)
% 4.69/4.87          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 4.69/4.87          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.69/4.87  thf('15', plain,
% 4.69/4.87      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.69/4.87        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['13', '14'])).
% 4.69/4.87  thf('16', plain,
% 4.69/4.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['12', '15'])).
% 4.69/4.87  thf('17', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('18', plain,
% 4.69/4.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.69/4.87         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 4.69/4.87          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 4.69/4.87          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.69/4.87  thf('19', plain,
% 4.69/4.87      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.69/4.87        | ((u1_struct_0 @ sk_A)
% 4.69/4.87            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['17', '18'])).
% 4.69/4.87  thf('20', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf(redefinition_k1_relset_1, axiom,
% 4.69/4.87    (![A:$i,B:$i,C:$i]:
% 4.69/4.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.69/4.87       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.69/4.87  thf('21', plain,
% 4.69/4.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.69/4.87         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 4.69/4.87          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 4.69/4.87      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.69/4.87  thf('22', plain,
% 4.69/4.87      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['20', '21'])).
% 4.69/4.87  thf('23', plain,
% 4.69/4.87      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.69/4.87        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['19', '22'])).
% 4.69/4.87  thf('24', plain,
% 4.69/4.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['16', '23'])).
% 4.69/4.87  thf('25', plain,
% 4.69/4.87      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 4.69/4.87        | ~ (l1_struct_0 @ sk_B)
% 4.69/4.87        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 4.69/4.87      inference('sup+', [status(thm)], ['9', '24'])).
% 4.69/4.87  thf('26', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf(redefinition_k2_relset_1, axiom,
% 4.69/4.87    (![A:$i,B:$i,C:$i]:
% 4.69/4.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.69/4.87       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.69/4.87  thf('27', plain,
% 4.69/4.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.69/4.87         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 4.69/4.87          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 4.69/4.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.69/4.87  thf('28', plain,
% 4.69/4.87      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['26', '27'])).
% 4.69/4.87  thf('29', plain,
% 4.69/4.87      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('32', plain,
% 4.69/4.87      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 4.69/4.87        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['25', '30', '31'])).
% 4.69/4.87  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf(fc5_struct_0, axiom,
% 4.69/4.87    (![A:$i]:
% 4.69/4.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.69/4.87       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 4.69/4.87  thf('34', plain,
% 4.69/4.87      (![X29 : $i]:
% 4.69/4.87         (~ (v1_xboole_0 @ (k2_struct_0 @ X29))
% 4.69/4.87          | ~ (l1_struct_0 @ X29)
% 4.69/4.87          | (v2_struct_0 @ X29))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc5_struct_0])).
% 4.69/4.87  thf('35', plain,
% 4.69/4.87      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 4.69/4.87        | (v2_struct_0 @ sk_B)
% 4.69/4.87        | ~ (l1_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup-', [status(thm)], ['33', '34'])).
% 4.69/4.87  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('37', plain,
% 4.69/4.87      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 4.69/4.87      inference('demod', [status(thm)], ['35', '36'])).
% 4.69/4.87  thf('38', plain, (~ (v2_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('39', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('clc', [status(thm)], ['37', '38'])).
% 4.69/4.87  thf('40', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('clc', [status(thm)], ['32', '39'])).
% 4.69/4.87  thf('41', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf('42', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('clc', [status(thm)], ['32', '39'])).
% 4.69/4.87  thf('43', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf('44', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('clc', [status(thm)], ['32', '39'])).
% 4.69/4.87  thf('45', plain,
% 4.69/4.87      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 4.69/4.87      inference('sup+', [status(thm)], ['43', '44'])).
% 4.69/4.87  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('47', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['45', '46'])).
% 4.69/4.87  thf('48', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf('49', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('50', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('clc', [status(thm)], ['32', '39'])).
% 4.69/4.87  thf('51', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('demod', [status(thm)], ['49', '50'])).
% 4.69/4.87  thf(d4_tops_2, axiom,
% 4.69/4.87    (![A:$i,B:$i,C:$i]:
% 4.69/4.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.69/4.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.69/4.87       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 4.69/4.87         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 4.69/4.87  thf('52', plain,
% 4.69/4.87      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.69/4.87         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 4.69/4.87          | ~ (v2_funct_1 @ X32)
% 4.69/4.87          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 4.69/4.87          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 4.69/4.87          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 4.69/4.87          | ~ (v1_funct_1 @ X32))),
% 4.69/4.87      inference('cnf', [status(esa)], [d4_tops_2])).
% 4.69/4.87  thf('53', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87            = (k2_funct_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87            != (u1_struct_0 @ sk_B)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['51', '52'])).
% 4.69/4.87  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('55', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('56', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('clc', [status(thm)], ['32', '39'])).
% 4.69/4.87  thf('57', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.69/4.87      inference('demod', [status(thm)], ['55', '56'])).
% 4.69/4.87  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('59', plain,
% 4.69/4.87      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['26', '27'])).
% 4.69/4.87  thf('60', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('clc', [status(thm)], ['32', '39'])).
% 4.69/4.87  thf('61', plain,
% 4.69/4.87      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['59', '60'])).
% 4.69/4.87  thf('62', plain,
% 4.69/4.87      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87          = (k2_funct_1 @ sk_C))
% 4.69/4.87        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.69/4.87      inference('demod', [status(thm)], ['53', '54', '57', '58', '61'])).
% 4.69/4.87  thf('63', plain,
% 4.69/4.87      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.69/4.87        | ~ (l1_struct_0 @ sk_B)
% 4.69/4.87        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87            = (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['48', '62'])).
% 4.69/4.87  thf('64', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('66', plain,
% 4.69/4.87      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.69/4.87        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87            = (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['63', '64', '65'])).
% 4.69/4.87  thf('67', plain,
% 4.69/4.87      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k2_funct_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['66'])).
% 4.69/4.87  thf('68', plain,
% 4.69/4.87      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87           (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87          sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['8', '40', '41', '42', '47', '67'])).
% 4.69/4.87  thf(fc6_funct_1, axiom,
% 4.69/4.87    (![A:$i]:
% 4.69/4.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 4.69/4.87       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.69/4.87         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 4.69/4.87         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.69/4.87  thf('69', plain,
% 4.69/4.87      (![X4 : $i]:
% 4.69/4.87         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 4.69/4.87          | ~ (v2_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_relat_1 @ X4))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.69/4.87  thf('70', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf('71', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('72', plain,
% 4.69/4.87      (((m1_subset_1 @ sk_C @ 
% 4.69/4.87         (k1_zfmisc_1 @ 
% 4.69/4.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 4.69/4.87        | ~ (l1_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['70', '71'])).
% 4.69/4.87  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('74', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 4.69/4.87      inference('demod', [status(thm)], ['72', '73'])).
% 4.69/4.87  thf('75', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf('76', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.69/4.87      inference('demod', [status(thm)], ['74', '75'])).
% 4.69/4.87  thf('77', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('clc', [status(thm)], ['32', '39'])).
% 4.69/4.87  thf('78', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.69/4.87      inference('demod', [status(thm)], ['76', '77'])).
% 4.69/4.87  thf(t31_funct_2, axiom,
% 4.69/4.87    (![A:$i,B:$i,C:$i]:
% 4.69/4.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.69/4.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.69/4.87       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.69/4.87         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.69/4.87           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.69/4.87           ( m1_subset_1 @
% 4.69/4.87             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 4.69/4.87  thf('79', plain,
% 4.69/4.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X25)
% 4.69/4.87          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 4.69/4.87          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 4.69/4.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.69/4.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 4.69/4.87          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 4.69/4.87          | ~ (v1_funct_1 @ X25))),
% 4.69/4.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.69/4.87  thf('80', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.69/4.87        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87           (k1_zfmisc_1 @ 
% 4.69/4.87            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 4.69/4.87        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.69/4.87            != (k2_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['78', '79'])).
% 4.69/4.87  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('82', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf('83', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('84', plain,
% 4.69/4.87      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 4.69/4.87        | ~ (l1_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['82', '83'])).
% 4.69/4.87  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('86', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('demod', [status(thm)], ['84', '85'])).
% 4.69/4.87  thf('87', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf('88', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['86', '87'])).
% 4.69/4.87  thf('89', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('clc', [status(thm)], ['32', '39'])).
% 4.69/4.87  thf('90', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['88', '89'])).
% 4.69/4.87  thf('91', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf('92', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf('93', plain,
% 4.69/4.87      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('94', plain,
% 4.69/4.87      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87          = (k2_struct_0 @ sk_B))
% 4.69/4.87        | ~ (l1_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['92', '93'])).
% 4.69/4.87  thf('95', plain, ((l1_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('96', plain,
% 4.69/4.87      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('demod', [status(thm)], ['94', '95'])).
% 4.69/4.87  thf('97', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf('99', plain,
% 4.69/4.87      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['96', '97', '98'])).
% 4.69/4.87  thf('100', plain,
% 4.69/4.87      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.69/4.87          = (k2_relat_1 @ sk_C))
% 4.69/4.87        | ~ (l1_struct_0 @ sk_A))),
% 4.69/4.87      inference('sup+', [status(thm)], ['91', '99'])).
% 4.69/4.87  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('102', plain,
% 4.69/4.87      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['100', '101'])).
% 4.69/4.87  thf('103', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['45', '46'])).
% 4.69/4.87  thf('104', plain,
% 4.69/4.87      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['102', '103'])).
% 4.69/4.87  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('106', plain,
% 4.69/4.87      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87         (k1_zfmisc_1 @ 
% 4.69/4.87          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 4.69/4.87        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['80', '81', '90', '104', '105'])).
% 4.69/4.87  thf('107', plain,
% 4.69/4.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.69/4.87      inference('simplify', [status(thm)], ['106'])).
% 4.69/4.87  thf('108', plain,
% 4.69/4.87      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.69/4.87         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 4.69/4.87          | ~ (v2_funct_1 @ X32)
% 4.69/4.87          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 4.69/4.87          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 4.69/4.87          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 4.69/4.87          | ~ (v1_funct_1 @ X32))),
% 4.69/4.87      inference('cnf', [status(esa)], [d4_tops_2])).
% 4.69/4.87  thf('109', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.69/4.87             (k1_relat_1 @ sk_C))
% 4.69/4.87        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['107', '108'])).
% 4.69/4.87  thf('110', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.69/4.87      inference('demod', [status(thm)], ['76', '77'])).
% 4.69/4.87  thf('111', plain,
% 4.69/4.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X25)
% 4.69/4.87          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 4.69/4.87          | (v1_funct_1 @ (k2_funct_1 @ X25))
% 4.69/4.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 4.69/4.87          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 4.69/4.87          | ~ (v1_funct_1 @ X25))),
% 4.69/4.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.69/4.87  thf('112', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.69/4.87            != (k2_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['110', '111'])).
% 4.69/4.87  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('114', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['88', '89'])).
% 4.69/4.87  thf('115', plain,
% 4.69/4.87      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['102', '103'])).
% 4.69/4.87  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('117', plain,
% 4.69/4.87      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 4.69/4.87  thf('118', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['117'])).
% 4.69/4.87  thf('119', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.69/4.87      inference('demod', [status(thm)], ['76', '77'])).
% 4.69/4.87  thf('120', plain,
% 4.69/4.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X25)
% 4.69/4.87          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 4.69/4.87          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 4.69/4.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 4.69/4.87          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 4.69/4.87          | ~ (v1_funct_1 @ X25))),
% 4.69/4.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.69/4.87  thf('121', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.69/4.87           (k1_relat_1 @ sk_C))
% 4.69/4.87        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.69/4.87            != (k2_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['119', '120'])).
% 4.69/4.87  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('123', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['88', '89'])).
% 4.69/4.87  thf('124', plain,
% 4.69/4.87      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['102', '103'])).
% 4.69/4.87  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('126', plain,
% 4.69/4.87      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.69/4.87         (k1_relat_1 @ sk_C))
% 4.69/4.87        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 4.69/4.87  thf('127', plain,
% 4.69/4.87      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.69/4.87        (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['126'])).
% 4.69/4.87  thf('128', plain,
% 4.69/4.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.69/4.87      inference('simplify', [status(thm)], ['106'])).
% 4.69/4.87  thf('129', plain,
% 4.69/4.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.69/4.87         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 4.69/4.87          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 4.69/4.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.69/4.87  thf('130', plain,
% 4.69/4.87      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['128', '129'])).
% 4.69/4.87  thf('131', plain,
% 4.69/4.87      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['109', '118', '127', '130'])).
% 4.69/4.87  thf(t65_funct_1, axiom,
% 4.69/4.87    (![A:$i]:
% 4.69/4.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.69/4.87       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 4.69/4.87  thf('132', plain,
% 4.69/4.87      (![X6 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X6)
% 4.69/4.87          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 4.69/4.87          | ~ (v1_funct_1 @ X6)
% 4.69/4.87          | ~ (v1_relat_1 @ X6))),
% 4.69/4.87      inference('cnf', [status(esa)], [t65_funct_1])).
% 4.69/4.87  thf(t55_funct_1, axiom,
% 4.69/4.87    (![A:$i]:
% 4.69/4.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.69/4.87       ( ( v2_funct_1 @ A ) =>
% 4.69/4.87         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.69/4.87           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.69/4.87  thf('133', plain,
% 4.69/4.87      (![X5 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X5)
% 4.69/4.87          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 4.69/4.87          | ~ (v1_funct_1 @ X5)
% 4.69/4.87          | ~ (v1_relat_1 @ X5))),
% 4.69/4.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.69/4.87  thf('134', plain,
% 4.69/4.87      (![X4 : $i]:
% 4.69/4.87         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 4.69/4.87          | ~ (v2_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_relat_1 @ X4))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.69/4.87  thf('135', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf('136', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('demod', [status(thm)], ['49', '50'])).
% 4.69/4.87  thf('137', plain,
% 4.69/4.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X25)
% 4.69/4.87          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 4.69/4.87          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 4.69/4.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.69/4.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 4.69/4.87          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 4.69/4.87          | ~ (v1_funct_1 @ X25))),
% 4.69/4.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.69/4.87  thf('138', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87           (k1_zfmisc_1 @ 
% 4.69/4.87            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 4.69/4.87        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87            != (u1_struct_0 @ sk_B))
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['136', '137'])).
% 4.69/4.87  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('140', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.69/4.87      inference('demod', [status(thm)], ['55', '56'])).
% 4.69/4.87  thf('141', plain,
% 4.69/4.87      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['59', '60'])).
% 4.69/4.87  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('143', plain,
% 4.69/4.87      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87         (k1_zfmisc_1 @ 
% 4.69/4.87          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 4.69/4.87        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.69/4.87      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 4.69/4.87  thf('144', plain,
% 4.69/4.87      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.69/4.87        | ~ (l1_struct_0 @ sk_B)
% 4.69/4.87        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87           (k1_zfmisc_1 @ 
% 4.69/4.87            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 4.69/4.87      inference('sup-', [status(thm)], ['135', '143'])).
% 4.69/4.87  thf('145', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('147', plain,
% 4.69/4.87      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.69/4.87        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87           (k1_zfmisc_1 @ 
% 4.69/4.87            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 4.69/4.87      inference('demod', [status(thm)], ['144', '145', '146'])).
% 4.69/4.87  thf('148', plain,
% 4.69/4.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.69/4.87      inference('simplify', [status(thm)], ['147'])).
% 4.69/4.87  thf('149', plain,
% 4.69/4.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X25)
% 4.69/4.87          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 4.69/4.87          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 4.69/4.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.69/4.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 4.69/4.87          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 4.69/4.87          | ~ (v1_funct_1 @ X25))),
% 4.69/4.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.69/4.87  thf('150', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87             (k1_relat_1 @ sk_C))
% 4.69/4.87        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_zfmisc_1 @ 
% 4.69/4.87            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.69/4.87        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['148', '149'])).
% 4.69/4.87  thf('151', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['117'])).
% 4.69/4.87  thf('152', plain,
% 4.69/4.87      (![X28 : $i]:
% 4.69/4.87         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 4.69/4.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.69/4.87  thf('153', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('demod', [status(thm)], ['49', '50'])).
% 4.69/4.87  thf('154', plain,
% 4.69/4.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X25)
% 4.69/4.87          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 4.69/4.87          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 4.69/4.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 4.69/4.87          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 4.69/4.87          | ~ (v1_funct_1 @ X25))),
% 4.69/4.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.69/4.87  thf('155', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87           (k1_relat_1 @ sk_C))
% 4.69/4.87        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87            != (u1_struct_0 @ sk_B))
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['153', '154'])).
% 4.69/4.87  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('157', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.69/4.87      inference('demod', [status(thm)], ['55', '56'])).
% 4.69/4.87  thf('158', plain,
% 4.69/4.87      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.69/4.87         = (k2_relat_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['59', '60'])).
% 4.69/4.87  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('160', plain,
% 4.69/4.87      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87         (k1_relat_1 @ sk_C))
% 4.69/4.87        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.69/4.87      inference('demod', [status(thm)], ['155', '156', '157', '158', '159'])).
% 4.69/4.87  thf('161', plain,
% 4.69/4.87      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.69/4.87        | ~ (l1_struct_0 @ sk_B)
% 4.69/4.87        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87           (k1_relat_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['152', '160'])).
% 4.69/4.87  thf('162', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.69/4.87      inference('sup+', [status(thm)], ['28', '29'])).
% 4.69/4.87  thf('163', plain, ((l1_struct_0 @ sk_B)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('164', plain,
% 4.69/4.87      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87           (k1_relat_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['161', '162', '163'])).
% 4.69/4.87  thf('165', plain,
% 4.69/4.87      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87        (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['164'])).
% 4.69/4.87  thf('166', plain,
% 4.69/4.87      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87         (k1_zfmisc_1 @ 
% 4.69/4.87          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.69/4.87        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['150', '151', '165'])).
% 4.69/4.87  thf('167', plain,
% 4.69/4.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.69/4.87      inference('simplify', [status(thm)], ['147'])).
% 4.69/4.87  thf('168', plain,
% 4.69/4.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.69/4.87         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 4.69/4.87          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 4.69/4.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.69/4.87  thf('169', plain,
% 4.69/4.87      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['167', '168'])).
% 4.69/4.87  thf('170', plain,
% 4.69/4.87      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87         (k1_zfmisc_1 @ 
% 4.69/4.87          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.69/4.87        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['166', '169'])).
% 4.69/4.87  thf('171', plain,
% 4.69/4.87      ((~ (v1_relat_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_zfmisc_1 @ 
% 4.69/4.87            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.69/4.87      inference('sup-', [status(thm)], ['134', '170'])).
% 4.69/4.87  thf('172', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf(cc2_relat_1, axiom,
% 4.69/4.87    (![A:$i]:
% 4.69/4.87     ( ( v1_relat_1 @ A ) =>
% 4.69/4.87       ( ![B:$i]:
% 4.69/4.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.69/4.87  thf('173', plain,
% 4.69/4.87      (![X0 : $i, X1 : $i]:
% 4.69/4.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 4.69/4.87          | (v1_relat_1 @ X0)
% 4.69/4.87          | ~ (v1_relat_1 @ X1))),
% 4.69/4.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.69/4.87  thf('174', plain,
% 4.69/4.87      ((~ (v1_relat_1 @ 
% 4.69/4.87           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 4.69/4.87        | (v1_relat_1 @ sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['172', '173'])).
% 4.69/4.87  thf(fc6_relat_1, axiom,
% 4.69/4.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.69/4.87  thf('175', plain,
% 4.69/4.87      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.69/4.87  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['174', '175'])).
% 4.69/4.87  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('178', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('179', plain,
% 4.69/4.87      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_zfmisc_1 @ 
% 4.69/4.87            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.69/4.87      inference('demod', [status(thm)], ['171', '176', '177', '178'])).
% 4.69/4.87  thf('180', plain,
% 4.69/4.87      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v1_relat_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_zfmisc_1 @ 
% 4.69/4.87            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.69/4.87      inference('sup-', [status(thm)], ['133', '179'])).
% 4.69/4.87  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['174', '175'])).
% 4.69/4.87  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('184', plain,
% 4.69/4.87      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_zfmisc_1 @ 
% 4.69/4.87            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.69/4.87      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 4.69/4.87  thf('185', plain,
% 4.69/4.87      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('simplify', [status(thm)], ['184'])).
% 4.69/4.87  thf('186', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('demod', [status(thm)], ['49', '50'])).
% 4.69/4.87  thf(redefinition_r2_funct_2, axiom,
% 4.69/4.87    (![A:$i,B:$i,C:$i,D:$i]:
% 4.69/4.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.69/4.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.69/4.87         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.69/4.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.69/4.87       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.69/4.87  thf('187', plain,
% 4.69/4.87      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 4.69/4.87         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 4.69/4.87          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 4.69/4.87          | ~ (v1_funct_1 @ X21)
% 4.69/4.87          | ~ (v1_funct_1 @ X24)
% 4.69/4.87          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 4.69/4.87          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 4.69/4.87          | ((X21) = (X24))
% 4.69/4.87          | ~ (r2_funct_2 @ X22 @ X23 @ X21 @ X24))),
% 4.69/4.87      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 4.69/4.87  thf('188', plain,
% 4.69/4.87      (![X0 : $i]:
% 4.69/4.87         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.69/4.87             X0)
% 4.69/4.87          | ((sk_C) = (X0))
% 4.69/4.87          | ~ (m1_subset_1 @ X0 @ 
% 4.69/4.87               (k1_zfmisc_1 @ 
% 4.69/4.87                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.69/4.87          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['186', '187'])).
% 4.69/4.87  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('190', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.69/4.87      inference('demod', [status(thm)], ['55', '56'])).
% 4.69/4.87  thf('191', plain,
% 4.69/4.87      (![X0 : $i]:
% 4.69/4.87         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.69/4.87             X0)
% 4.69/4.87          | ((sk_C) = (X0))
% 4.69/4.87          | ~ (m1_subset_1 @ X0 @ 
% 4.69/4.87               (k1_zfmisc_1 @ 
% 4.69/4.87                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.69/4.87          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87          | ~ (v1_funct_1 @ X0))),
% 4.69/4.87      inference('demod', [status(thm)], ['188', '189', '190'])).
% 4.69/4.87  thf('192', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87             (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.69/4.87             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.69/4.87      inference('sup-', [status(thm)], ['185', '191'])).
% 4.69/4.87  thf('193', plain,
% 4.69/4.87      (![X5 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X5)
% 4.69/4.87          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 4.69/4.87          | ~ (v1_funct_1 @ X5)
% 4.69/4.87          | ~ (v1_relat_1 @ X5))),
% 4.69/4.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.69/4.87  thf('194', plain,
% 4.69/4.87      (![X4 : $i]:
% 4.69/4.87         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 4.69/4.87          | ~ (v2_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_relat_1 @ X4))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.69/4.87  thf('195', plain,
% 4.69/4.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.69/4.87      inference('simplify', [status(thm)], ['147'])).
% 4.69/4.87  thf('196', plain,
% 4.69/4.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X25)
% 4.69/4.87          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 4.69/4.87          | (v1_funct_1 @ (k2_funct_1 @ X25))
% 4.69/4.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 4.69/4.87          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 4.69/4.87          | ~ (v1_funct_1 @ X25))),
% 4.69/4.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.69/4.87  thf('197', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87             (k1_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['195', '196'])).
% 4.69/4.87  thf('198', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['117'])).
% 4.69/4.87  thf('199', plain,
% 4.69/4.87      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87        (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['164'])).
% 4.69/4.87  thf('200', plain,
% 4.69/4.87      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['197', '198', '199'])).
% 4.69/4.87  thf('201', plain,
% 4.69/4.87      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['167', '168'])).
% 4.69/4.87  thf('202', plain,
% 4.69/4.87      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['200', '201'])).
% 4.69/4.87  thf('203', plain,
% 4.69/4.87      ((~ (v1_relat_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.69/4.87      inference('sup-', [status(thm)], ['194', '202'])).
% 4.69/4.87  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['174', '175'])).
% 4.69/4.87  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('206', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('207', plain,
% 4.69/4.87      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.69/4.87      inference('demod', [status(thm)], ['203', '204', '205', '206'])).
% 4.69/4.87  thf('208', plain,
% 4.69/4.87      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v1_relat_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.69/4.87      inference('sup-', [status(thm)], ['193', '207'])).
% 4.69/4.87  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['174', '175'])).
% 4.69/4.87  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('211', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('212', plain,
% 4.69/4.87      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.69/4.87      inference('demod', [status(thm)], ['208', '209', '210', '211'])).
% 4.69/4.87  thf('213', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('simplify', [status(thm)], ['212'])).
% 4.69/4.87  thf('214', plain,
% 4.69/4.87      (![X5 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X5)
% 4.69/4.87          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 4.69/4.87          | ~ (v1_funct_1 @ X5)
% 4.69/4.87          | ~ (v1_relat_1 @ X5))),
% 4.69/4.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.69/4.87  thf('215', plain,
% 4.69/4.87      (![X4 : $i]:
% 4.69/4.87         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 4.69/4.87          | ~ (v2_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_relat_1 @ X4))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.69/4.87  thf('216', plain,
% 4.69/4.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.69/4.87      inference('simplify', [status(thm)], ['147'])).
% 4.69/4.87  thf('217', plain,
% 4.69/4.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X25)
% 4.69/4.87          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 4.69/4.87          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 4.69/4.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 4.69/4.87          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 4.69/4.87          | ~ (v1_funct_1 @ X25))),
% 4.69/4.87      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.69/4.87  thf('218', plain,
% 4.69/4.87      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87             (k1_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['216', '217'])).
% 4.69/4.87  thf('219', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['117'])).
% 4.69/4.87  thf('220', plain,
% 4.69/4.87      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.69/4.87        (k1_relat_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['164'])).
% 4.69/4.87  thf('221', plain,
% 4.69/4.87      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['218', '219', '220'])).
% 4.69/4.87  thf('222', plain,
% 4.69/4.87      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['167', '168'])).
% 4.69/4.87  thf('223', plain,
% 4.69/4.87      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['221', '222'])).
% 4.69/4.87  thf('224', plain,
% 4.69/4.87      ((~ (v1_relat_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['215', '223'])).
% 4.69/4.87  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['174', '175'])).
% 4.69/4.87  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('228', plain,
% 4.69/4.87      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.69/4.87      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 4.69/4.87  thf('229', plain,
% 4.69/4.87      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | ~ (v1_relat_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['214', '228'])).
% 4.69/4.87  thf('230', plain, ((v1_relat_1 @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['174', '175'])).
% 4.69/4.87  thf('231', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('232', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('233', plain,
% 4.69/4.87      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.69/4.87        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.69/4.87      inference('demod', [status(thm)], ['229', '230', '231', '232'])).
% 4.69/4.87  thf('234', plain,
% 4.69/4.87      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.69/4.87        (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.69/4.87      inference('simplify', [status(thm)], ['233'])).
% 4.69/4.87  thf('235', plain,
% 4.69/4.87      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.69/4.87             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.69/4.87      inference('demod', [status(thm)], ['192', '213', '234'])).
% 4.69/4.87  thf('236', plain,
% 4.69/4.87      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.69/4.87           sk_C)
% 4.69/4.87        | ~ (v1_relat_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.69/4.87      inference('sup-', [status(thm)], ['132', '235'])).
% 4.69/4.87  thf('237', plain,
% 4.69/4.87      ((m1_subset_1 @ sk_C @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.69/4.87      inference('demod', [status(thm)], ['49', '50'])).
% 4.69/4.87  thf('238', plain,
% 4.69/4.87      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 4.69/4.87         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 4.69/4.87          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 4.69/4.87          | ~ (v1_funct_1 @ X21)
% 4.69/4.87          | ~ (v1_funct_1 @ X24)
% 4.69/4.87          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 4.69/4.87          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 4.69/4.87          | (r2_funct_2 @ X22 @ X23 @ X21 @ X24)
% 4.69/4.87          | ((X21) != (X24)))),
% 4.69/4.87      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 4.69/4.87  thf('239', plain,
% 4.69/4.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.69/4.87         ((r2_funct_2 @ X22 @ X23 @ X24 @ X24)
% 4.69/4.87          | ~ (v1_funct_1 @ X24)
% 4.69/4.87          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 4.69/4.87          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.69/4.87      inference('simplify', [status(thm)], ['238'])).
% 4.69/4.87  thf('240', plain,
% 4.69/4.87      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.69/4.87           sk_C))),
% 4.69/4.87      inference('sup-', [status(thm)], ['237', '239'])).
% 4.69/4.87  thf('241', plain,
% 4.69/4.87      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.69/4.87      inference('demod', [status(thm)], ['55', '56'])).
% 4.69/4.87  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('243', plain,
% 4.69/4.87      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['240', '241', '242'])).
% 4.69/4.87  thf('244', plain, ((v1_relat_1 @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['174', '175'])).
% 4.69/4.87  thf('245', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('246', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('247', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['236', '243', '244', '245', '246'])).
% 4.69/4.87  thf('248', plain,
% 4.69/4.87      (![X4 : $i]:
% 4.69/4.87         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 4.69/4.87          | ~ (v2_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_relat_1 @ X4))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.69/4.87  thf('249', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['236', '243', '244', '245', '246'])).
% 4.69/4.87  thf('250', plain,
% 4.69/4.87      (![X4 : $i]:
% 4.69/4.87         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 4.69/4.87          | ~ (v2_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_relat_1 @ X4))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.69/4.87  thf('251', plain,
% 4.69/4.87      (![X4 : $i]:
% 4.69/4.87         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 4.69/4.87          | ~ (v2_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_relat_1 @ X4))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.69/4.87  thf('252', plain,
% 4.69/4.87      (![X4 : $i]:
% 4.69/4.87         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 4.69/4.87          | ~ (v2_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_funct_1 @ X4)
% 4.69/4.87          | ~ (v1_relat_1 @ X4))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.69/4.87  thf('253', plain,
% 4.69/4.87      (![X6 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X6)
% 4.69/4.87          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 4.69/4.87          | ~ (v1_funct_1 @ X6)
% 4.69/4.87          | ~ (v1_relat_1 @ X6))),
% 4.69/4.87      inference('cnf', [status(esa)], [t65_funct_1])).
% 4.69/4.87  thf('254', plain,
% 4.69/4.87      (![X5 : $i]:
% 4.69/4.87         (~ (v2_funct_1 @ X5)
% 4.69/4.87          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 4.69/4.87          | ~ (v1_funct_1 @ X5)
% 4.69/4.87          | ~ (v1_relat_1 @ X5))),
% 4.69/4.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.69/4.87  thf('255', plain,
% 4.69/4.87      (![X0 : $i]:
% 4.69/4.87         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 4.69/4.87          | ~ (v1_relat_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.69/4.87          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.69/4.87          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 4.69/4.87      inference('sup+', [status(thm)], ['253', '254'])).
% 4.69/4.87  thf('256', plain,
% 4.69/4.87      (![X0 : $i]:
% 4.69/4.87         (~ (v1_relat_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 4.69/4.87          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_relat_1 @ X0)
% 4.69/4.87          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['252', '255'])).
% 4.69/4.87  thf('257', plain,
% 4.69/4.87      (![X0 : $i]:
% 4.69/4.87         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 4.69/4.87          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.69/4.87          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_relat_1 @ X0))),
% 4.69/4.87      inference('simplify', [status(thm)], ['256'])).
% 4.69/4.87  thf('258', plain,
% 4.69/4.87      (![X0 : $i]:
% 4.69/4.87         (~ (v1_relat_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_relat_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 4.69/4.87          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['251', '257'])).
% 4.69/4.87  thf('259', plain,
% 4.69/4.87      (![X0 : $i]:
% 4.69/4.87         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 4.69/4.87          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_relat_1 @ X0))),
% 4.69/4.87      inference('simplify', [status(thm)], ['258'])).
% 4.69/4.87  thf('260', plain,
% 4.69/4.87      (![X0 : $i]:
% 4.69/4.87         (~ (v1_relat_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_relat_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['250', '259'])).
% 4.69/4.87  thf('261', plain,
% 4.69/4.87      (![X0 : $i]:
% 4.69/4.87         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 4.69/4.87          | ~ (v2_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_funct_1 @ X0)
% 4.69/4.87          | ~ (v1_relat_1 @ X0))),
% 4.69/4.87      inference('simplify', [status(thm)], ['260'])).
% 4.69/4.87  thf('262', plain,
% 4.69/4.87      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup+', [status(thm)], ['249', '261'])).
% 4.69/4.87  thf('263', plain,
% 4.69/4.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.69/4.87        (k1_zfmisc_1 @ 
% 4.69/4.87         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.69/4.87      inference('simplify', [status(thm)], ['106'])).
% 4.69/4.87  thf('264', plain,
% 4.69/4.87      (![X0 : $i, X1 : $i]:
% 4.69/4.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 4.69/4.87          | (v1_relat_1 @ X0)
% 4.69/4.87          | ~ (v1_relat_1 @ X1))),
% 4.69/4.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.69/4.87  thf('265', plain,
% 4.69/4.87      ((~ (v1_relat_1 @ 
% 4.69/4.87           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 4.69/4.87        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['263', '264'])).
% 4.69/4.87  thf('266', plain,
% 4.69/4.87      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 4.69/4.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.69/4.87  thf('267', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['265', '266'])).
% 4.69/4.87  thf('268', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.69/4.87      inference('simplify', [status(thm)], ['117'])).
% 4.69/4.87  thf('269', plain,
% 4.69/4.87      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['262', '267', '268'])).
% 4.69/4.87  thf('270', plain,
% 4.69/4.87      ((~ (v1_relat_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 4.69/4.87      inference('sup-', [status(thm)], ['248', '269'])).
% 4.69/4.87  thf('271', plain, ((v1_relat_1 @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['174', '175'])).
% 4.69/4.87  thf('272', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('273', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('274', plain,
% 4.69/4.87      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['270', '271', '272', '273'])).
% 4.69/4.87  thf('275', plain,
% 4.69/4.87      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87          (k2_funct_1 @ sk_C)) = (sk_C))
% 4.69/4.87        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 4.69/4.87      inference('demod', [status(thm)], ['131', '247', '274'])).
% 4.69/4.87  thf('276', plain,
% 4.69/4.87      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.69/4.87        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 4.69/4.87      inference('simplify', [status(thm)], ['275'])).
% 4.69/4.87  thf('277', plain,
% 4.69/4.87      ((~ (v1_relat_1 @ sk_C)
% 4.69/4.87        | ~ (v1_funct_1 @ sk_C)
% 4.69/4.87        | ~ (v2_funct_1 @ sk_C)
% 4.69/4.87        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 4.69/4.87      inference('sup-', [status(thm)], ['69', '276'])).
% 4.69/4.87  thf('278', plain, ((v1_relat_1 @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['174', '175'])).
% 4.69/4.87  thf('279', plain, ((v1_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('280', plain, ((v2_funct_1 @ sk_C)),
% 4.69/4.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.69/4.87  thf('281', plain,
% 4.69/4.87      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.69/4.87         (k2_funct_1 @ sk_C)) = (sk_C))),
% 4.69/4.87      inference('demod', [status(thm)], ['277', '278', '279', '280'])).
% 4.69/4.87  thf('282', plain,
% 4.69/4.87      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 4.69/4.87      inference('demod', [status(thm)], ['240', '241', '242'])).
% 4.69/4.87  thf('283', plain, ($false),
% 4.69/4.87      inference('demod', [status(thm)], ['68', '281', '282'])).
% 4.69/4.87  
% 4.69/4.87  % SZS output end Refutation
% 4.69/4.87  
% 4.69/4.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
