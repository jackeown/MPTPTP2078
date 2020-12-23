%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mPKIbI6Anp

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:11 EST 2020

% Result     : Theorem 5.21s
% Output     : Refutation 5.21s
% Verified   : 
% Statistics : Number of formulae       :  310 (9348 expanded)
%              Number of leaves         :   44 (2723 expanded)
%              Depth                    :   35
%              Number of atoms          : 2947 (205246 expanded)
%              Number of equality atoms :  162 (6989 expanded)
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

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
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

thf('43',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('45',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

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

thf('54',plain,(
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

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('74',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('81',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['55','56','65','66','84'])).

thf('86',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','40','41','42','43','44','86'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

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

thf('90',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('91',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('94',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
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

thf('99',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('101',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('110',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('114',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('117',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('119',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('120',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['99','108','117','120'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('122',plain,(
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

thf('123',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('125',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('130',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('136',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131','134','137','138'])).

thf('140',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['125','139'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('142',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('146',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['107'])).

thf('148',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('150',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('151',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('154',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['148','156'])).

thf('158',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('159',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['146','147','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('164',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('165',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','165'])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['124','166'])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('169',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['167','170','171','172'])).

thf('174',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['123','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['168','169'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['174','175','176','177'])).

thf('179',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

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

thf('181',plain,(
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

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['179','185'])).

thf('187',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('189',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('190',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('191',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['107'])).

thf('193',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['160'])).

thf('194',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('196',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['188','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['168','169'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['187','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['168','169'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['202','203','204','205'])).

thf('207',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('210',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('211',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('212',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['107'])).

thf('214',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['160'])).

thf('215',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('217',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['209','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['168','169'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('223',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['208','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['168','169'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['223','224','225','226'])).

thf('228',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['186','207','228'])).

thf('230',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['122','229'])).

thf('231',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('232',plain,(
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

thf('233',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_funct_2 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['231','233'])).

thf('235',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('236',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['168','169'])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['230','237','238','239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('243',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['230','237','238','239','240'])).

thf('244',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('245',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['243','244'])).

thf('246',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('247',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('248',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['107'])).

thf('250',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['245','248','249'])).

thf('251',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['242','250'])).

thf('252',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['168','169'])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('256',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','241','255'])).

thf('257',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['88','257'])).

thf('259',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['168','169'])).

thf('260',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['258','259','260','261'])).

thf('263',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('264',plain,(
    $false ),
    inference(demod,[status(thm)],['87','262','263'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mPKIbI6Anp
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:24:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.21/5.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.21/5.42  % Solved by: fo/fo7.sh
% 5.21/5.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.21/5.42  % done 1182 iterations in 4.954s
% 5.21/5.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.21/5.42  % SZS output start Refutation
% 5.21/5.42  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.21/5.42  thf(sk_C_type, type, sk_C: $i).
% 5.21/5.42  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.21/5.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.21/5.42  thf(sk_B_type, type, sk_B: $i).
% 5.21/5.42  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.21/5.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.21/5.42  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.21/5.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.21/5.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.21/5.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.21/5.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.21/5.42  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 5.21/5.42  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.21/5.42  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.21/5.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.21/5.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.21/5.42  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 5.21/5.42  thf(sk_A_type, type, sk_A: $i).
% 5.21/5.42  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.21/5.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.21/5.42  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.21/5.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.21/5.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.21/5.42  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.21/5.42  thf(d3_struct_0, axiom,
% 5.21/5.42    (![A:$i]:
% 5.21/5.42     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.21/5.42  thf('0', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf('1', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf(t64_tops_2, conjecture,
% 5.21/5.42    (![A:$i]:
% 5.21/5.42     ( ( l1_struct_0 @ A ) =>
% 5.21/5.42       ( ![B:$i]:
% 5.21/5.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 5.21/5.42           ( ![C:$i]:
% 5.21/5.42             ( ( ( v1_funct_1 @ C ) & 
% 5.21/5.42                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.21/5.42                 ( m1_subset_1 @
% 5.21/5.42                   C @ 
% 5.21/5.42                   ( k1_zfmisc_1 @
% 5.21/5.42                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.21/5.42               ( ( ( ( k2_relset_1 @
% 5.21/5.42                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 5.21/5.42                     ( k2_struct_0 @ B ) ) & 
% 5.21/5.42                   ( v2_funct_1 @ C ) ) =>
% 5.21/5.42                 ( r2_funct_2 @
% 5.21/5.42                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 5.21/5.42                   ( k2_tops_2 @
% 5.21/5.42                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.21/5.42                     ( k2_tops_2 @
% 5.21/5.42                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 5.21/5.42                   C ) ) ) ) ) ) ))).
% 5.21/5.42  thf(zf_stmt_0, negated_conjecture,
% 5.21/5.42    (~( ![A:$i]:
% 5.21/5.42        ( ( l1_struct_0 @ A ) =>
% 5.21/5.42          ( ![B:$i]:
% 5.21/5.42            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 5.21/5.42              ( ![C:$i]:
% 5.21/5.42                ( ( ( v1_funct_1 @ C ) & 
% 5.21/5.42                    ( v1_funct_2 @
% 5.21/5.42                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.21/5.42                    ( m1_subset_1 @
% 5.21/5.42                      C @ 
% 5.21/5.42                      ( k1_zfmisc_1 @
% 5.21/5.42                        ( k2_zfmisc_1 @
% 5.21/5.42                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.21/5.42                  ( ( ( ( k2_relset_1 @
% 5.21/5.42                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 5.21/5.42                        ( k2_struct_0 @ B ) ) & 
% 5.21/5.42                      ( v2_funct_1 @ C ) ) =>
% 5.21/5.42                    ( r2_funct_2 @
% 5.21/5.42                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 5.21/5.42                      ( k2_tops_2 @
% 5.21/5.42                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.21/5.42                        ( k2_tops_2 @
% 5.21/5.42                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 5.21/5.42                      C ) ) ) ) ) ) ) )),
% 5.21/5.42    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 5.21/5.42  thf('2', plain,
% 5.21/5.42      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.21/5.42           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 5.21/5.42          sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('3', plain,
% 5.21/5.42      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.21/5.42            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 5.21/5.42           sk_C)
% 5.21/5.42        | ~ (l1_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup-', [status(thm)], ['1', '2'])).
% 5.21/5.42  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('5', plain,
% 5.21/5.42      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.21/5.42           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 5.21/5.42          sk_C)),
% 5.21/5.42      inference('demod', [status(thm)], ['3', '4'])).
% 5.21/5.42  thf('6', plain,
% 5.21/5.42      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.21/5.42            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 5.21/5.42           sk_C)
% 5.21/5.42        | ~ (l1_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup-', [status(thm)], ['0', '5'])).
% 5.21/5.42  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('8', plain,
% 5.21/5.42      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.21/5.42           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 5.21/5.42          sk_C)),
% 5.21/5.42      inference('demod', [status(thm)], ['6', '7'])).
% 5.21/5.42  thf('9', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf(d1_funct_2, axiom,
% 5.21/5.42    (![A:$i,B:$i,C:$i]:
% 5.21/5.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.42       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.21/5.42           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.21/5.42             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.21/5.42         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.21/5.42           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.21/5.42             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.21/5.42  thf(zf_stmt_1, axiom,
% 5.21/5.42    (![B:$i,A:$i]:
% 5.21/5.42     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.21/5.42       ( zip_tseitin_0 @ B @ A ) ))).
% 5.21/5.42  thf('10', plain,
% 5.21/5.42      (![X12 : $i, X13 : $i]:
% 5.21/5.42         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.21/5.42  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.21/5.42  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.21/5.42      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.21/5.42  thf('12', plain,
% 5.21/5.42      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.21/5.42      inference('sup+', [status(thm)], ['10', '11'])).
% 5.21/5.42  thf('13', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.21/5.42  thf(zf_stmt_3, axiom,
% 5.21/5.42    (![C:$i,B:$i,A:$i]:
% 5.21/5.42     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.21/5.42       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.21/5.42  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.21/5.42  thf(zf_stmt_5, axiom,
% 5.21/5.42    (![A:$i,B:$i,C:$i]:
% 5.21/5.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.42       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.21/5.42         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.21/5.42           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.21/5.42             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.21/5.42  thf('14', plain,
% 5.21/5.42      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.21/5.42         (~ (zip_tseitin_0 @ X17 @ X18)
% 5.21/5.42          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 5.21/5.42          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.21/5.42  thf('15', plain,
% 5.21/5.42      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.21/5.42        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['13', '14'])).
% 5.21/5.42  thf('16', plain,
% 5.21/5.42      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 5.21/5.42        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['12', '15'])).
% 5.21/5.42  thf('17', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('18', plain,
% 5.21/5.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.21/5.42         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 5.21/5.42          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 5.21/5.42          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.21/5.42  thf('19', plain,
% 5.21/5.42      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.21/5.42        | ((u1_struct_0 @ sk_A)
% 5.21/5.42            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['17', '18'])).
% 5.21/5.42  thf('20', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf(redefinition_k1_relset_1, axiom,
% 5.21/5.42    (![A:$i,B:$i,C:$i]:
% 5.21/5.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.42       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.21/5.42  thf('21', plain,
% 5.21/5.42      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.21/5.42         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 5.21/5.42          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 5.21/5.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.21/5.42  thf('22', plain,
% 5.21/5.42      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42         = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['20', '21'])).
% 5.21/5.42  thf('23', plain,
% 5.21/5.42      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.21/5.42        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['19', '22'])).
% 5.21/5.42  thf('24', plain,
% 5.21/5.42      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 5.21/5.42        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['16', '23'])).
% 5.21/5.42  thf('25', plain,
% 5.21/5.42      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 5.21/5.42        | ~ (l1_struct_0 @ sk_B)
% 5.21/5.42        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('sup+', [status(thm)], ['9', '24'])).
% 5.21/5.42  thf('26', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf(redefinition_k2_relset_1, axiom,
% 5.21/5.42    (![A:$i,B:$i,C:$i]:
% 5.21/5.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.42       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.21/5.42  thf('27', plain,
% 5.21/5.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.21/5.42         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 5.21/5.42          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 5.21/5.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.21/5.42  thf('28', plain,
% 5.21/5.42      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['26', '27'])).
% 5.21/5.42  thf('29', plain,
% 5.21/5.42      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42         = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['28', '29'])).
% 5.21/5.42  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('32', plain,
% 5.21/5.42      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 5.21/5.42        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['25', '30', '31'])).
% 5.21/5.42  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['28', '29'])).
% 5.21/5.42  thf(fc5_struct_0, axiom,
% 5.21/5.42    (![A:$i]:
% 5.21/5.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 5.21/5.42       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 5.21/5.42  thf('34', plain,
% 5.21/5.42      (![X28 : $i]:
% 5.21/5.42         (~ (v1_xboole_0 @ (k2_struct_0 @ X28))
% 5.21/5.42          | ~ (l1_struct_0 @ X28)
% 5.21/5.42          | (v2_struct_0 @ X28))),
% 5.21/5.42      inference('cnf', [status(esa)], [fc5_struct_0])).
% 5.21/5.42  thf('35', plain,
% 5.21/5.42      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 5.21/5.42        | (v2_struct_0 @ sk_B)
% 5.21/5.42        | ~ (l1_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup-', [status(thm)], ['33', '34'])).
% 5.21/5.42  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('37', plain,
% 5.21/5.42      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 5.21/5.42      inference('demod', [status(thm)], ['35', '36'])).
% 5.21/5.42  thf('38', plain, (~ (v2_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('39', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['37', '38'])).
% 5.21/5.42  thf('40', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['32', '39'])).
% 5.21/5.42  thf('41', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['28', '29'])).
% 5.21/5.42  thf('42', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['32', '39'])).
% 5.21/5.42  thf('43', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['32', '39'])).
% 5.21/5.42  thf('44', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['28', '29'])).
% 5.21/5.42  thf('45', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf('46', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('47', plain,
% 5.21/5.42      (((m1_subset_1 @ sk_C @ 
% 5.21/5.42         (k1_zfmisc_1 @ 
% 5.21/5.42          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 5.21/5.42        | ~ (l1_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['45', '46'])).
% 5.21/5.42  thf('48', plain, ((l1_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('49', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 5.21/5.42      inference('demod', [status(thm)], ['47', '48'])).
% 5.21/5.42  thf('50', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['28', '29'])).
% 5.21/5.42  thf('51', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 5.21/5.42      inference('demod', [status(thm)], ['49', '50'])).
% 5.21/5.42  thf('52', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['32', '39'])).
% 5.21/5.42  thf('53', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.21/5.42      inference('demod', [status(thm)], ['51', '52'])).
% 5.21/5.42  thf(d4_tops_2, axiom,
% 5.21/5.42    (![A:$i,B:$i,C:$i]:
% 5.21/5.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.21/5.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.21/5.42       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 5.21/5.42         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 5.21/5.42  thf('54', plain,
% 5.21/5.42      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.21/5.42         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 5.21/5.42          | ~ (v2_funct_1 @ X31)
% 5.21/5.42          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 5.21/5.42          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 5.21/5.42          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 5.21/5.42          | ~ (v1_funct_1 @ X31))),
% 5.21/5.42      inference('cnf', [status(esa)], [d4_tops_2])).
% 5.21/5.42  thf('55', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.21/5.42        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42            = (k2_funct_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42            != (k2_relat_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['53', '54'])).
% 5.21/5.42  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('57', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf('58', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('59', plain,
% 5.21/5.42      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 5.21/5.42        | ~ (l1_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['57', '58'])).
% 5.21/5.42  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('61', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('demod', [status(thm)], ['59', '60'])).
% 5.21/5.42  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['28', '29'])).
% 5.21/5.42  thf('63', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['61', '62'])).
% 5.21/5.42  thf('64', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['32', '39'])).
% 5.21/5.42  thf('65', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['63', '64'])).
% 5.21/5.42  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('67', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf('68', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf('69', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('70', plain,
% 5.21/5.42      (((m1_subset_1 @ sk_C @ 
% 5.21/5.42         (k1_zfmisc_1 @ 
% 5.21/5.42          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 5.21/5.42        | ~ (l1_struct_0 @ sk_A))),
% 5.21/5.42      inference('sup+', [status(thm)], ['68', '69'])).
% 5.21/5.42  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('72', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('demod', [status(thm)], ['70', '71'])).
% 5.21/5.42  thf('73', plain,
% 5.21/5.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.21/5.42         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 5.21/5.42          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 5.21/5.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.21/5.42  thf('74', plain,
% 5.21/5.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['72', '73'])).
% 5.21/5.42  thf('75', plain,
% 5.21/5.42      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42          = (k2_relat_1 @ sk_C))
% 5.21/5.42        | ~ (l1_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['67', '74'])).
% 5.21/5.42  thf('76', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['28', '29'])).
% 5.21/5.42  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('78', plain,
% 5.21/5.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['75', '76', '77'])).
% 5.21/5.42  thf('79', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf('80', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['32', '39'])).
% 5.21/5.42  thf('81', plain,
% 5.21/5.42      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 5.21/5.42      inference('sup+', [status(thm)], ['79', '80'])).
% 5.21/5.42  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('83', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['81', '82'])).
% 5.21/5.42  thf('84', plain,
% 5.21/5.42      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['78', '83'])).
% 5.21/5.42  thf('85', plain,
% 5.21/5.42      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42          = (k2_funct_1 @ sk_C))
% 5.21/5.42        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['55', '56', '65', '66', '84'])).
% 5.21/5.42  thf('86', plain,
% 5.21/5.42      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42         = (k2_funct_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['85'])).
% 5.21/5.42  thf('87', plain,
% 5.21/5.42      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42           (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42          sk_C)),
% 5.21/5.42      inference('demod', [status(thm)],
% 5.21/5.42                ['8', '40', '41', '42', '43', '44', '86'])).
% 5.21/5.42  thf(fc6_funct_1, axiom,
% 5.21/5.42    (![A:$i]:
% 5.21/5.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 5.21/5.42       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.21/5.42         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 5.21/5.42         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.21/5.42  thf('88', plain,
% 5.21/5.42      (![X0 : $i]:
% 5.21/5.42         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.21/5.42          | ~ (v2_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_relat_1 @ X0))),
% 5.21/5.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.21/5.42  thf('89', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.21/5.42      inference('demod', [status(thm)], ['51', '52'])).
% 5.21/5.42  thf(t31_funct_2, axiom,
% 5.21/5.42    (![A:$i,B:$i,C:$i]:
% 5.21/5.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.21/5.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.21/5.42       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.21/5.42         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.21/5.42           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.21/5.42           ( m1_subset_1 @
% 5.21/5.42             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 5.21/5.42  thf('90', plain,
% 5.21/5.42      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X24)
% 5.21/5.42          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.21/5.42          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 5.21/5.42             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.21/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.21/5.42          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.21/5.42          | ~ (v1_funct_1 @ X24))),
% 5.21/5.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.21/5.42  thf('91', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.21/5.42        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42           (k1_zfmisc_1 @ 
% 5.21/5.42            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 5.21/5.42        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42            != (k2_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['89', '90'])).
% 5.21/5.42  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('93', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['63', '64'])).
% 5.21/5.42  thf('94', plain,
% 5.21/5.42      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['78', '83'])).
% 5.21/5.42  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('96', plain,
% 5.21/5.42      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42         (k1_zfmisc_1 @ 
% 5.21/5.42          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 5.21/5.42        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 5.21/5.42  thf('97', plain,
% 5.21/5.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 5.21/5.42      inference('simplify', [status(thm)], ['96'])).
% 5.21/5.42  thf('98', plain,
% 5.21/5.42      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.21/5.42         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 5.21/5.42          | ~ (v2_funct_1 @ X31)
% 5.21/5.42          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 5.21/5.42          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 5.21/5.42          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 5.21/5.42          | ~ (v1_funct_1 @ X31))),
% 5.21/5.42      inference('cnf', [status(esa)], [d4_tops_2])).
% 5.21/5.42  thf('99', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 5.21/5.42             (k1_relat_1 @ sk_C))
% 5.21/5.42        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['97', '98'])).
% 5.21/5.42  thf('100', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.21/5.42      inference('demod', [status(thm)], ['51', '52'])).
% 5.21/5.42  thf('101', plain,
% 5.21/5.42      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X24)
% 5.21/5.42          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.21/5.42          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 5.21/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.21/5.42          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.21/5.42          | ~ (v1_funct_1 @ X24))),
% 5.21/5.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.21/5.42  thf('102', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42            != (k2_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['100', '101'])).
% 5.21/5.42  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('104', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['63', '64'])).
% 5.21/5.42  thf('105', plain,
% 5.21/5.42      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['78', '83'])).
% 5.21/5.42  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('107', plain,
% 5.21/5.42      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 5.21/5.42  thf('108', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['107'])).
% 5.21/5.42  thf('109', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.21/5.42      inference('demod', [status(thm)], ['51', '52'])).
% 5.21/5.42  thf('110', plain,
% 5.21/5.42      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X24)
% 5.21/5.42          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.21/5.42          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 5.21/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.21/5.42          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.21/5.42          | ~ (v1_funct_1 @ X24))),
% 5.21/5.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.21/5.42  thf('111', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 5.21/5.42           (k1_relat_1 @ sk_C))
% 5.21/5.42        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42            != (k2_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['109', '110'])).
% 5.21/5.42  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('113', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['63', '64'])).
% 5.21/5.42  thf('114', plain,
% 5.21/5.42      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['78', '83'])).
% 5.21/5.42  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('116', plain,
% 5.21/5.42      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 5.21/5.42         (k1_relat_1 @ sk_C))
% 5.21/5.42        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 5.21/5.42  thf('117', plain,
% 5.21/5.42      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 5.21/5.42        (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['116'])).
% 5.21/5.42  thf('118', plain,
% 5.21/5.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 5.21/5.42      inference('simplify', [status(thm)], ['96'])).
% 5.21/5.42  thf('119', plain,
% 5.21/5.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.21/5.42         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 5.21/5.42          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 5.21/5.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.21/5.42  thf('120', plain,
% 5.21/5.42      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['118', '119'])).
% 5.21/5.42  thf('121', plain,
% 5.21/5.42      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['99', '108', '117', '120'])).
% 5.21/5.42  thf(t65_funct_1, axiom,
% 5.21/5.42    (![A:$i]:
% 5.21/5.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.21/5.42       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 5.21/5.42  thf('122', plain,
% 5.21/5.42      (![X2 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X2)
% 5.21/5.42          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 5.21/5.42          | ~ (v1_funct_1 @ X2)
% 5.21/5.42          | ~ (v1_relat_1 @ X2))),
% 5.21/5.42      inference('cnf', [status(esa)], [t65_funct_1])).
% 5.21/5.42  thf(t55_funct_1, axiom,
% 5.21/5.42    (![A:$i]:
% 5.21/5.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.21/5.42       ( ( v2_funct_1 @ A ) =>
% 5.21/5.42         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.21/5.42           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.21/5.42  thf('123', plain,
% 5.21/5.42      (![X1 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X1)
% 5.21/5.42          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 5.21/5.42          | ~ (v1_funct_1 @ X1)
% 5.21/5.42          | ~ (v1_relat_1 @ X1))),
% 5.21/5.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.21/5.42  thf('124', plain,
% 5.21/5.42      (![X0 : $i]:
% 5.21/5.42         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.21/5.42          | ~ (v2_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_relat_1 @ X0))),
% 5.21/5.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.21/5.42  thf('125', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf('126', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('127', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['32', '39'])).
% 5.21/5.42  thf('128', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('demod', [status(thm)], ['126', '127'])).
% 5.21/5.42  thf('129', plain,
% 5.21/5.42      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X24)
% 5.21/5.42          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.21/5.42          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 5.21/5.42             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.21/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.21/5.42          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.21/5.42          | ~ (v1_funct_1 @ X24))),
% 5.21/5.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.21/5.42  thf('130', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.21/5.42        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42           (k1_zfmisc_1 @ 
% 5.21/5.42            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 5.21/5.42        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42            != (u1_struct_0 @ sk_B))
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['128', '129'])).
% 5.21/5.42  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('132', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('133', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['32', '39'])).
% 5.21/5.42  thf('134', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.21/5.42      inference('demod', [status(thm)], ['132', '133'])).
% 5.21/5.42  thf('135', plain,
% 5.21/5.42      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['26', '27'])).
% 5.21/5.42  thf('136', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('clc', [status(thm)], ['32', '39'])).
% 5.21/5.42  thf('137', plain,
% 5.21/5.42      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['135', '136'])).
% 5.21/5.42  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('139', plain,
% 5.21/5.42      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42         (k1_zfmisc_1 @ 
% 5.21/5.42          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 5.21/5.42        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 5.21/5.42      inference('demod', [status(thm)], ['130', '131', '134', '137', '138'])).
% 5.21/5.42  thf('140', plain,
% 5.21/5.42      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 5.21/5.42        | ~ (l1_struct_0 @ sk_B)
% 5.21/5.42        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42           (k1_zfmisc_1 @ 
% 5.21/5.42            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 5.21/5.42      inference('sup-', [status(thm)], ['125', '139'])).
% 5.21/5.42  thf('141', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['28', '29'])).
% 5.21/5.42  thf('142', plain, ((l1_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('143', plain,
% 5.21/5.42      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 5.21/5.42        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42           (k1_zfmisc_1 @ 
% 5.21/5.42            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 5.21/5.42      inference('demod', [status(thm)], ['140', '141', '142'])).
% 5.21/5.42  thf('144', plain,
% 5.21/5.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.21/5.42      inference('simplify', [status(thm)], ['143'])).
% 5.21/5.42  thf('145', plain,
% 5.21/5.42      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X24)
% 5.21/5.42          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.21/5.42          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 5.21/5.42             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.21/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.21/5.42          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.21/5.42          | ~ (v1_funct_1 @ X24))),
% 5.21/5.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.21/5.42  thf('146', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42             (k1_relat_1 @ sk_C))
% 5.21/5.42        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_zfmisc_1 @ 
% 5.21/5.42            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.21/5.42        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['144', '145'])).
% 5.21/5.42  thf('147', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['107'])).
% 5.21/5.42  thf('148', plain,
% 5.21/5.42      (![X27 : $i]:
% 5.21/5.42         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.21/5.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.21/5.42  thf('149', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('demod', [status(thm)], ['126', '127'])).
% 5.21/5.42  thf('150', plain,
% 5.21/5.42      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X24)
% 5.21/5.42          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.21/5.42          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 5.21/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.21/5.42          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.21/5.42          | ~ (v1_funct_1 @ X24))),
% 5.21/5.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.21/5.42  thf('151', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.21/5.42        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42           (k1_relat_1 @ sk_C))
% 5.21/5.42        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42            != (u1_struct_0 @ sk_B))
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['149', '150'])).
% 5.21/5.42  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('153', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.21/5.42      inference('demod', [status(thm)], ['132', '133'])).
% 5.21/5.42  thf('154', plain,
% 5.21/5.42      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.21/5.42         = (k2_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['135', '136'])).
% 5.21/5.42  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('156', plain,
% 5.21/5.42      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42         (k1_relat_1 @ sk_C))
% 5.21/5.42        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 5.21/5.42      inference('demod', [status(thm)], ['151', '152', '153', '154', '155'])).
% 5.21/5.42  thf('157', plain,
% 5.21/5.42      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 5.21/5.42        | ~ (l1_struct_0 @ sk_B)
% 5.21/5.42        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42           (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['148', '156'])).
% 5.21/5.42  thf('158', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.21/5.42      inference('sup+', [status(thm)], ['28', '29'])).
% 5.21/5.42  thf('159', plain, ((l1_struct_0 @ sk_B)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('160', plain,
% 5.21/5.42      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42           (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['157', '158', '159'])).
% 5.21/5.42  thf('161', plain,
% 5.21/5.42      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42        (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['160'])).
% 5.21/5.42  thf('162', plain,
% 5.21/5.42      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42         (k1_zfmisc_1 @ 
% 5.21/5.42          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.21/5.42        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['146', '147', '161'])).
% 5.21/5.42  thf('163', plain,
% 5.21/5.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.21/5.42      inference('simplify', [status(thm)], ['143'])).
% 5.21/5.42  thf('164', plain,
% 5.21/5.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.21/5.42         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 5.21/5.42          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 5.21/5.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.21/5.42  thf('165', plain,
% 5.21/5.42      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['163', '164'])).
% 5.21/5.42  thf('166', plain,
% 5.21/5.42      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42         (k1_zfmisc_1 @ 
% 5.21/5.42          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.21/5.42        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['162', '165'])).
% 5.21/5.42  thf('167', plain,
% 5.21/5.42      ((~ (v1_relat_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_zfmisc_1 @ 
% 5.21/5.42            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.21/5.42      inference('sup-', [status(thm)], ['124', '166'])).
% 5.21/5.42  thf('168', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf(cc1_relset_1, axiom,
% 5.21/5.42    (![A:$i,B:$i,C:$i]:
% 5.21/5.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.42       ( v1_relat_1 @ C ) ))).
% 5.21/5.42  thf('169', plain,
% 5.21/5.42      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.21/5.42         ((v1_relat_1 @ X3)
% 5.21/5.42          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 5.21/5.42      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.21/5.42  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 5.21/5.42      inference('sup-', [status(thm)], ['168', '169'])).
% 5.21/5.42  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('173', plain,
% 5.21/5.42      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_zfmisc_1 @ 
% 5.21/5.42            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.21/5.42      inference('demod', [status(thm)], ['167', '170', '171', '172'])).
% 5.21/5.42  thf('174', plain,
% 5.21/5.42      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v1_relat_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_zfmisc_1 @ 
% 5.21/5.42            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.21/5.42      inference('sup-', [status(thm)], ['123', '173'])).
% 5.21/5.42  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 5.21/5.42      inference('sup-', [status(thm)], ['168', '169'])).
% 5.21/5.42  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('177', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('178', plain,
% 5.21/5.42      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_zfmisc_1 @ 
% 5.21/5.42            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.21/5.42      inference('demod', [status(thm)], ['174', '175', '176', '177'])).
% 5.21/5.42  thf('179', plain,
% 5.21/5.42      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('simplify', [status(thm)], ['178'])).
% 5.21/5.42  thf('180', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('demod', [status(thm)], ['126', '127'])).
% 5.21/5.42  thf(redefinition_r2_funct_2, axiom,
% 5.21/5.42    (![A:$i,B:$i,C:$i,D:$i]:
% 5.21/5.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.21/5.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.21/5.42         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.21/5.42         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.21/5.42       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.21/5.42  thf('181', plain,
% 5.21/5.42      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 5.21/5.42         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 5.21/5.42          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 5.21/5.42          | ~ (v1_funct_1 @ X20)
% 5.21/5.42          | ~ (v1_funct_1 @ X23)
% 5.21/5.42          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 5.21/5.42          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 5.21/5.42          | ((X20) = (X23))
% 5.21/5.42          | ~ (r2_funct_2 @ X21 @ X22 @ X20 @ X23))),
% 5.21/5.42      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 5.21/5.42  thf('182', plain,
% 5.21/5.42      (![X0 : $i]:
% 5.21/5.42         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.21/5.42             X0)
% 5.21/5.42          | ((sk_C) = (X0))
% 5.21/5.42          | ~ (m1_subset_1 @ X0 @ 
% 5.21/5.42               (k1_zfmisc_1 @ 
% 5.21/5.42                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.21/5.42          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.21/5.42          | ~ (v1_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['180', '181'])).
% 5.21/5.42  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('184', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.21/5.42      inference('demod', [status(thm)], ['132', '133'])).
% 5.21/5.42  thf('185', plain,
% 5.21/5.42      (![X0 : $i]:
% 5.21/5.42         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.21/5.42             X0)
% 5.21/5.42          | ((sk_C) = (X0))
% 5.21/5.42          | ~ (m1_subset_1 @ X0 @ 
% 5.21/5.42               (k1_zfmisc_1 @ 
% 5.21/5.42                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.21/5.42          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.21/5.42          | ~ (v1_funct_1 @ X0))),
% 5.21/5.42      inference('demod', [status(thm)], ['182', '183', '184'])).
% 5.21/5.42  thf('186', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.21/5.42        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42             (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.21/5.42        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.21/5.42        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.21/5.42             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.21/5.42      inference('sup-', [status(thm)], ['179', '185'])).
% 5.21/5.42  thf('187', plain,
% 5.21/5.42      (![X1 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X1)
% 5.21/5.42          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 5.21/5.42          | ~ (v1_funct_1 @ X1)
% 5.21/5.42          | ~ (v1_relat_1 @ X1))),
% 5.21/5.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.21/5.42  thf('188', plain,
% 5.21/5.42      (![X0 : $i]:
% 5.21/5.42         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.21/5.42          | ~ (v2_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_relat_1 @ X0))),
% 5.21/5.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.21/5.42  thf('189', plain,
% 5.21/5.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.21/5.42      inference('simplify', [status(thm)], ['143'])).
% 5.21/5.42  thf('190', plain,
% 5.21/5.42      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X24)
% 5.21/5.42          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.21/5.42          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 5.21/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.21/5.42          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.21/5.42          | ~ (v1_funct_1 @ X24))),
% 5.21/5.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.21/5.42  thf('191', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42             (k1_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.21/5.42        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['189', '190'])).
% 5.21/5.42  thf('192', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['107'])).
% 5.21/5.42  thf('193', plain,
% 5.21/5.42      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42        (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['160'])).
% 5.21/5.42  thf('194', plain,
% 5.21/5.42      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.21/5.42        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['191', '192', '193'])).
% 5.21/5.42  thf('195', plain,
% 5.21/5.42      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['163', '164'])).
% 5.21/5.42  thf('196', plain,
% 5.21/5.42      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.21/5.42        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['194', '195'])).
% 5.21/5.42  thf('197', plain,
% 5.21/5.42      ((~ (v1_relat_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.21/5.42      inference('sup-', [status(thm)], ['188', '196'])).
% 5.21/5.42  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 5.21/5.42      inference('sup-', [status(thm)], ['168', '169'])).
% 5.21/5.42  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('201', plain,
% 5.21/5.42      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.21/5.42      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 5.21/5.42  thf('202', plain,
% 5.21/5.42      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v1_relat_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.21/5.42      inference('sup-', [status(thm)], ['187', '201'])).
% 5.21/5.42  thf('203', plain, ((v1_relat_1 @ sk_C)),
% 5.21/5.42      inference('sup-', [status(thm)], ['168', '169'])).
% 5.21/5.42  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('205', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('206', plain,
% 5.21/5.42      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.21/5.42      inference('demod', [status(thm)], ['202', '203', '204', '205'])).
% 5.21/5.42  thf('207', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('simplify', [status(thm)], ['206'])).
% 5.21/5.42  thf('208', plain,
% 5.21/5.42      (![X1 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X1)
% 5.21/5.42          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 5.21/5.42          | ~ (v1_funct_1 @ X1)
% 5.21/5.42          | ~ (v1_relat_1 @ X1))),
% 5.21/5.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.21/5.42  thf('209', plain,
% 5.21/5.42      (![X0 : $i]:
% 5.21/5.42         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.21/5.42          | ~ (v2_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_relat_1 @ X0))),
% 5.21/5.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.21/5.42  thf('210', plain,
% 5.21/5.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.21/5.42      inference('simplify', [status(thm)], ['143'])).
% 5.21/5.42  thf('211', plain,
% 5.21/5.42      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X24)
% 5.21/5.42          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.21/5.42          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 5.21/5.42          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.21/5.42          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.21/5.42          | ~ (v1_funct_1 @ X24))),
% 5.21/5.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.21/5.42  thf('212', plain,
% 5.21/5.42      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42             (k1_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.21/5.42        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['210', '211'])).
% 5.21/5.42  thf('213', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['107'])).
% 5.21/5.42  thf('214', plain,
% 5.21/5.42      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.21/5.42        (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['160'])).
% 5.21/5.42  thf('215', plain,
% 5.21/5.42      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.21/5.42        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['212', '213', '214'])).
% 5.21/5.42  thf('216', plain,
% 5.21/5.42      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['163', '164'])).
% 5.21/5.42  thf('217', plain,
% 5.21/5.42      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.21/5.42        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['215', '216'])).
% 5.21/5.42  thf('218', plain,
% 5.21/5.42      ((~ (v1_relat_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['209', '217'])).
% 5.21/5.42  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 5.21/5.42      inference('sup-', [status(thm)], ['168', '169'])).
% 5.21/5.42  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('221', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('222', plain,
% 5.21/5.42      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.21/5.42      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 5.21/5.42  thf('223', plain,
% 5.21/5.42      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v1_relat_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['208', '222'])).
% 5.21/5.42  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 5.21/5.42      inference('sup-', [status(thm)], ['168', '169'])).
% 5.21/5.42  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('226', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('227', plain,
% 5.21/5.42      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.21/5.42        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.21/5.42      inference('demod', [status(thm)], ['223', '224', '225', '226'])).
% 5.21/5.42  thf('228', plain,
% 5.21/5.42      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.21/5.42        (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.21/5.42      inference('simplify', [status(thm)], ['227'])).
% 5.21/5.42  thf('229', plain,
% 5.21/5.42      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.21/5.42        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.21/5.42             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.21/5.42      inference('demod', [status(thm)], ['186', '207', '228'])).
% 5.21/5.42  thf('230', plain,
% 5.21/5.42      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.21/5.42           sk_C)
% 5.21/5.42        | ~ (v1_relat_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.21/5.42      inference('sup-', [status(thm)], ['122', '229'])).
% 5.21/5.42  thf('231', plain,
% 5.21/5.42      ((m1_subset_1 @ sk_C @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.21/5.42      inference('demod', [status(thm)], ['126', '127'])).
% 5.21/5.42  thf('232', plain,
% 5.21/5.42      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 5.21/5.42         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 5.21/5.42          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 5.21/5.42          | ~ (v1_funct_1 @ X20)
% 5.21/5.42          | ~ (v1_funct_1 @ X23)
% 5.21/5.42          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 5.21/5.42          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 5.21/5.42          | (r2_funct_2 @ X21 @ X22 @ X20 @ X23)
% 5.21/5.42          | ((X20) != (X23)))),
% 5.21/5.42      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 5.21/5.42  thf('233', plain,
% 5.21/5.42      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.21/5.42         ((r2_funct_2 @ X21 @ X22 @ X23 @ X23)
% 5.21/5.42          | ~ (v1_funct_1 @ X23)
% 5.21/5.42          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 5.21/5.42          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.21/5.42      inference('simplify', [status(thm)], ['232'])).
% 5.21/5.42  thf('234', plain,
% 5.21/5.42      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.21/5.42           sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['231', '233'])).
% 5.21/5.42  thf('235', plain,
% 5.21/5.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.21/5.42      inference('demod', [status(thm)], ['132', '133'])).
% 5.21/5.42  thf('236', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('237', plain,
% 5.21/5.42      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 5.21/5.42      inference('demod', [status(thm)], ['234', '235', '236'])).
% 5.21/5.42  thf('238', plain, ((v1_relat_1 @ sk_C)),
% 5.21/5.42      inference('sup-', [status(thm)], ['168', '169'])).
% 5.21/5.42  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('240', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('241', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['230', '237', '238', '239', '240'])).
% 5.21/5.42  thf('242', plain,
% 5.21/5.42      (![X0 : $i]:
% 5.21/5.42         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.21/5.42          | ~ (v2_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_funct_1 @ X0)
% 5.21/5.42          | ~ (v1_relat_1 @ X0))),
% 5.21/5.42      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.21/5.42  thf('243', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['230', '237', '238', '239', '240'])).
% 5.21/5.42  thf('244', plain,
% 5.21/5.42      (![X1 : $i]:
% 5.21/5.42         (~ (v2_funct_1 @ X1)
% 5.21/5.42          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 5.21/5.42          | ~ (v1_funct_1 @ X1)
% 5.21/5.42          | ~ (v1_relat_1 @ X1))),
% 5.21/5.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.21/5.42  thf('245', plain,
% 5.21/5.42      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('sup+', [status(thm)], ['243', '244'])).
% 5.21/5.42  thf('246', plain,
% 5.21/5.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.21/5.42        (k1_zfmisc_1 @ 
% 5.21/5.42         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 5.21/5.42      inference('simplify', [status(thm)], ['96'])).
% 5.21/5.42  thf('247', plain,
% 5.21/5.42      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.21/5.42         ((v1_relat_1 @ X3)
% 5.21/5.42          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 5.21/5.42      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.21/5.42  thf('248', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 5.21/5.42      inference('sup-', [status(thm)], ['246', '247'])).
% 5.21/5.42  thf('249', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.21/5.42      inference('simplify', [status(thm)], ['107'])).
% 5.21/5.42  thf('250', plain,
% 5.21/5.42      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['245', '248', '249'])).
% 5.21/5.42  thf('251', plain,
% 5.21/5.42      ((~ (v1_relat_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['242', '250'])).
% 5.21/5.42  thf('252', plain, ((v1_relat_1 @ sk_C)),
% 5.21/5.42      inference('sup-', [status(thm)], ['168', '169'])).
% 5.21/5.42  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('254', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('255', plain,
% 5.21/5.42      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 5.21/5.42  thf('256', plain,
% 5.21/5.42      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42          (k2_funct_1 @ sk_C)) = (sk_C))
% 5.21/5.42        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 5.21/5.42      inference('demod', [status(thm)], ['121', '241', '255'])).
% 5.21/5.42  thf('257', plain,
% 5.21/5.42      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.21/5.42        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 5.21/5.42      inference('simplify', [status(thm)], ['256'])).
% 5.21/5.42  thf('258', plain,
% 5.21/5.42      ((~ (v1_relat_1 @ sk_C)
% 5.21/5.42        | ~ (v1_funct_1 @ sk_C)
% 5.21/5.42        | ~ (v2_funct_1 @ sk_C)
% 5.21/5.42        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 5.21/5.42      inference('sup-', [status(thm)], ['88', '257'])).
% 5.21/5.42  thf('259', plain, ((v1_relat_1 @ sk_C)),
% 5.21/5.42      inference('sup-', [status(thm)], ['168', '169'])).
% 5.21/5.42  thf('260', plain, ((v1_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('261', plain, ((v2_funct_1 @ sk_C)),
% 5.21/5.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.42  thf('262', plain,
% 5.21/5.42      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 5.21/5.42         (k2_funct_1 @ sk_C)) = (sk_C))),
% 5.21/5.42      inference('demod', [status(thm)], ['258', '259', '260', '261'])).
% 5.21/5.42  thf('263', plain,
% 5.21/5.42      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 5.21/5.42      inference('demod', [status(thm)], ['234', '235', '236'])).
% 5.21/5.42  thf('264', plain, ($false),
% 5.21/5.42      inference('demod', [status(thm)], ['87', '262', '263'])).
% 5.21/5.42  
% 5.21/5.42  % SZS output end Refutation
% 5.21/5.42  
% 5.21/5.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
