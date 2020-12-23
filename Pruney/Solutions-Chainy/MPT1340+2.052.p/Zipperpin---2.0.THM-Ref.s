%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5BLNvWjhMl

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:15 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  270 (1888 expanded)
%              Number of leaves         :   46 ( 576 expanded)
%              Depth                    :   21
%              Number of atoms          : 2254 (39738 expanded)
%              Number of equality atoms :  122 (1134 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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

thf('9',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','37'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48'])).

thf('50',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('52',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('58',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','64'])).

thf('66',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('68',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','65'])).

thf('69',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','65'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('71',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','66','67','68','69','70'])).

thf('72',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

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

thf('79',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('111',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','92','98','99','111'])).

thf('113',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
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

thf('115',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('119',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('120',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('127',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('128',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('133',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('137',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('138',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139'])).

thf('141',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('143',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('144',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('150',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('151',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

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

thf('156',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('157',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('158',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('162',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('163',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('164',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('165',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('166',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('167',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('168',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['166','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['165','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['164','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['163','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['162','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('180',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['161','181'])).

thf('183',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('184',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('185',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('188',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('189',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('190',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('191',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['182','183','184','185','186','187','188','189','190'])).

thf('192',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('193',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('194',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('195',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','191','192','198'])).

thf('200',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('202',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('203',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['182','183','184','185','186','187','188','189','190'])).

thf('205',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','64'])).

thf('206',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['203','206'])).

thf('208',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','131','141','148','200','207'])).

thf('209',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['71','113','209'])).

thf('211',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('212',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('213',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['211','217'])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('221',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,(
    $false ),
    inference(demod,[status(thm)],['210','221'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5BLNvWjhMl
% 0.14/0.36  % Computer   : n002.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 18:12:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.58/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.78  % Solved by: fo/fo7.sh
% 0.58/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.78  % done 519 iterations in 0.303s
% 0.58/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.78  % SZS output start Refutation
% 0.58/0.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.78  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.78  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.58/0.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.78  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.58/0.78  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.58/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.78  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.58/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.78  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.58/0.78  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.58/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.58/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.78  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.58/0.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.78  thf(d3_struct_0, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.58/0.78  thf('0', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('1', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf(t64_tops_2, conjecture,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_struct_0 @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.58/0.78           ( ![C:$i]:
% 0.58/0.78             ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.78                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.78                 ( m1_subset_1 @
% 0.58/0.78                   C @ 
% 0.58/0.78                   ( k1_zfmisc_1 @
% 0.58/0.78                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.78               ( ( ( ( k2_relset_1 @
% 0.58/0.78                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.58/0.78                     ( k2_struct_0 @ B ) ) & 
% 0.58/0.78                   ( v2_funct_1 @ C ) ) =>
% 0.58/0.78                 ( r2_funct_2 @
% 0.58/0.78                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.78                   ( k2_tops_2 @
% 0.58/0.78                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.58/0.78                     ( k2_tops_2 @
% 0.58/0.78                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.58/0.78                   C ) ) ) ) ) ) ))).
% 0.58/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.78    (~( ![A:$i]:
% 0.58/0.78        ( ( l1_struct_0 @ A ) =>
% 0.58/0.78          ( ![B:$i]:
% 0.58/0.78            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.58/0.78              ( ![C:$i]:
% 0.58/0.78                ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.78                    ( v1_funct_2 @
% 0.58/0.78                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.78                    ( m1_subset_1 @
% 0.58/0.78                      C @ 
% 0.58/0.78                      ( k1_zfmisc_1 @
% 0.58/0.78                        ( k2_zfmisc_1 @
% 0.58/0.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.78                  ( ( ( ( k2_relset_1 @
% 0.58/0.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.58/0.78                        ( k2_struct_0 @ B ) ) & 
% 0.58/0.78                      ( v2_funct_1 @ C ) ) =>
% 0.58/0.78                    ( r2_funct_2 @
% 0.58/0.78                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.78                      ( k2_tops_2 @
% 0.58/0.78                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.58/0.78                        ( k2_tops_2 @
% 0.58/0.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.58/0.78                      C ) ) ) ) ) ) ) )),
% 0.58/0.78    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.58/0.78  thf('2', plain,
% 0.58/0.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.78          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.58/0.78          sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('3', plain,
% 0.58/0.78      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.78           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.58/0.78           sk_C)
% 0.58/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.78  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('5', plain,
% 0.58/0.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.78          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.58/0.78          sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['3', '4'])).
% 0.58/0.78  thf('6', plain,
% 0.58/0.78      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.78           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.58/0.78           sk_C)
% 0.58/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['0', '5'])).
% 0.58/0.78  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('8', plain,
% 0.58/0.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.78          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.58/0.78          sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['6', '7'])).
% 0.58/0.78  thf('9', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('10', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('11', plain,
% 0.58/0.78      (((m1_subset_1 @ sk_C @ 
% 0.58/0.78         (k1_zfmisc_1 @ 
% 0.58/0.78          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['9', '10'])).
% 0.58/0.78  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('13', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['11', '12'])).
% 0.58/0.78  thf('14', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(redefinition_k2_relset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.78       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.58/0.78  thf('15', plain,
% 0.58/0.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.78         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.58/0.78          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.58/0.78  thf('16', plain,
% 0.58/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.58/0.78         = (k2_relat_1 @ sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.78  thf('17', plain,
% 0.58/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.58/0.78         = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('18', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('19', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.58/0.78      inference('demod', [status(thm)], ['13', '18'])).
% 0.58/0.78  thf(cc5_funct_2, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.58/0.78       ( ![C:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.78           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.58/0.78             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.58/0.78  thf('20', plain,
% 0.58/0.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.58/0.78          | (v1_partfun1 @ X19 @ X20)
% 0.58/0.78          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.58/0.78          | ~ (v1_funct_1 @ X19)
% 0.58/0.78          | (v1_xboole_0 @ X21))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.58/0.78  thf('21', plain,
% 0.58/0.78      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.58/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.58/0.78        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.78  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('23', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('24', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('25', plain,
% 0.58/0.78      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['23', '24'])).
% 0.58/0.78  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('27', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['25', '26'])).
% 0.58/0.78  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('29', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['27', '28'])).
% 0.58/0.78  thf('30', plain,
% 0.58/0.78      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.58/0.78        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['21', '22', '29'])).
% 0.58/0.78  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf(fc5_struct_0, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.58/0.78       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.58/0.78  thf('32', plain,
% 0.58/0.78      (![X32 : $i]:
% 0.58/0.78         (~ (v1_xboole_0 @ (k2_struct_0 @ X32))
% 0.58/0.78          | ~ (l1_struct_0 @ X32)
% 0.58/0.78          | (v2_struct_0 @ X32))),
% 0.58/0.78      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.58/0.78  thf('33', plain,
% 0.58/0.78      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.58/0.78        | (v2_struct_0 @ sk_B)
% 0.58/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['31', '32'])).
% 0.58/0.78  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('35', plain,
% 0.58/0.78      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['33', '34'])).
% 0.58/0.78  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('37', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.58/0.78      inference('clc', [status(thm)], ['35', '36'])).
% 0.58/0.78  thf('38', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.58/0.78      inference('clc', [status(thm)], ['30', '37'])).
% 0.58/0.78  thf(d4_partfun1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.58/0.78       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.58/0.78  thf('39', plain,
% 0.58/0.78      (![X22 : $i, X23 : $i]:
% 0.58/0.78         (~ (v1_partfun1 @ X23 @ X22)
% 0.58/0.78          | ((k1_relat_1 @ X23) = (X22))
% 0.58/0.78          | ~ (v4_relat_1 @ X23 @ X22)
% 0.58/0.78          | ~ (v1_relat_1 @ X23))),
% 0.58/0.78      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.58/0.78  thf('40', plain,
% 0.58/0.78      ((~ (v1_relat_1 @ sk_C)
% 0.58/0.78        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.58/0.78        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.78  thf('41', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(cc2_relat_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( v1_relat_1 @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.58/0.78  thf('42', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.58/0.78          | (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X1))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.78  thf('43', plain,
% 0.58/0.78      ((~ (v1_relat_1 @ 
% 0.58/0.78           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.58/0.78        | (v1_relat_1 @ sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['41', '42'])).
% 0.58/0.78  thf(fc6_relat_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.58/0.78  thf('44', plain,
% 0.58/0.78      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.78  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('46', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(cc2_relset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.78  thf('47', plain,
% 0.58/0.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.78         ((v4_relat_1 @ X13 @ X14)
% 0.58/0.78          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.78  thf('48', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.78  thf('49', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['40', '45', '48'])).
% 0.58/0.78  thf('50', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('51', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.58/0.78      inference('clc', [status(thm)], ['30', '37'])).
% 0.58/0.78  thf('52', plain,
% 0.58/0.78      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['50', '51'])).
% 0.58/0.78  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('54', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['52', '53'])).
% 0.58/0.78  thf('55', plain,
% 0.58/0.78      (![X22 : $i, X23 : $i]:
% 0.58/0.78         (~ (v1_partfun1 @ X23 @ X22)
% 0.58/0.78          | ((k1_relat_1 @ X23) = (X22))
% 0.58/0.78          | ~ (v4_relat_1 @ X23 @ X22)
% 0.58/0.78          | ~ (v1_relat_1 @ X23))),
% 0.58/0.78      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.58/0.78  thf('56', plain,
% 0.58/0.78      ((~ (v1_relat_1 @ sk_C)
% 0.58/0.78        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.58/0.78        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.78  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('58', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('59', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('60', plain,
% 0.58/0.78      (((m1_subset_1 @ sk_C @ 
% 0.58/0.78         (k1_zfmisc_1 @ 
% 0.58/0.78          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['58', '59'])).
% 0.58/0.78  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('62', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['60', '61'])).
% 0.58/0.78  thf('63', plain,
% 0.58/0.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.78         ((v4_relat_1 @ X13 @ X14)
% 0.58/0.78          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.78  thf('64', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['62', '63'])).
% 0.58/0.78  thf('65', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['56', '57', '64'])).
% 0.58/0.78  thf('66', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['49', '65'])).
% 0.58/0.78  thf('67', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('68', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['49', '65'])).
% 0.58/0.78  thf('69', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['49', '65'])).
% 0.58/0.78  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('71', plain,
% 0.58/0.78      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.78          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.58/0.78          sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['8', '66', '67', '68', '69', '70'])).
% 0.58/0.78  thf('72', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('73', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['60', '61'])).
% 0.58/0.78  thf('74', plain,
% 0.58/0.78      (((m1_subset_1 @ sk_C @ 
% 0.58/0.78         (k1_zfmisc_1 @ 
% 0.58/0.78          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['72', '73'])).
% 0.58/0.78  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('76', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['74', '75'])).
% 0.58/0.78  thf('77', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('78', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.58/0.78      inference('demod', [status(thm)], ['76', '77'])).
% 0.58/0.78  thf(d4_tops_2, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.78       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.58/0.78         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.58/0.78  thf('79', plain,
% 0.58/0.78      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.58/0.78         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.58/0.78          | ~ (v2_funct_1 @ X35)
% 0.58/0.78          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.58/0.78          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.58/0.78          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.58/0.78          | ~ (v1_funct_1 @ X35))),
% 0.58/0.78      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.58/0.78  thf('80', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.58/0.78        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78            = (k2_funct_1 @ sk_C))
% 0.58/0.78        | ~ (v2_funct_1 @ sk_C)
% 0.58/0.78        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78            != (k2_relat_1 @ sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['78', '79'])).
% 0.58/0.78  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('82', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('83', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('84', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('85', plain,
% 0.58/0.78      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['83', '84'])).
% 0.58/0.78  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('87', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['85', '86'])).
% 0.58/0.78  thf('88', plain,
% 0.58/0.78      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['82', '87'])).
% 0.58/0.78  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('90', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['88', '89'])).
% 0.58/0.78  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('92', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['90', '91'])).
% 0.58/0.78  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(d9_funct_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.78       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.58/0.78  thf('94', plain,
% 0.58/0.78      (![X5 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X5)
% 0.58/0.78          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.58/0.78          | ~ (v1_funct_1 @ X5)
% 0.58/0.78          | ~ (v1_relat_1 @ X5))),
% 0.58/0.78      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.58/0.78  thf('95', plain,
% 0.58/0.78      ((~ (v1_relat_1 @ sk_C)
% 0.58/0.78        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.58/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['93', '94'])).
% 0.58/0.78  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('98', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('100', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('101', plain,
% 0.58/0.78      (![X31 : $i]:
% 0.58/0.78         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.78  thf('102', plain,
% 0.58/0.78      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.58/0.78         = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('103', plain,
% 0.58/0.78      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.58/0.78          = (k2_struct_0 @ sk_B))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['101', '102'])).
% 0.58/0.78  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('105', plain,
% 0.58/0.78      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.58/0.78         = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['103', '104'])).
% 0.58/0.78  thf('106', plain,
% 0.58/0.78      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.58/0.78          = (k2_struct_0 @ sk_B))
% 0.58/0.78        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['100', '105'])).
% 0.58/0.78  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('108', plain,
% 0.58/0.78      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.58/0.78         = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['106', '107'])).
% 0.58/0.78  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('110', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('111', plain,
% 0.58/0.78      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78         = (k2_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.58/0.78  thf('112', plain,
% 0.58/0.78      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78          = (k4_relat_1 @ sk_C))
% 0.58/0.78        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.58/0.78      inference('demod', [status(thm)], ['80', '81', '92', '98', '99', '111'])).
% 0.58/0.78  thf('113', plain,
% 0.58/0.78      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78         = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('simplify', [status(thm)], ['112'])).
% 0.58/0.78  thf('114', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.58/0.78      inference('demod', [status(thm)], ['76', '77'])).
% 0.58/0.78  thf(t31_funct_2, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.78       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.58/0.78         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.58/0.78           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.58/0.78           ( m1_subset_1 @
% 0.58/0.78             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.58/0.78  thf('115', plain,
% 0.58/0.78      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X28)
% 0.58/0.78          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.58/0.78          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 0.58/0.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.58/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.58/0.78          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.58/0.78          | ~ (v1_funct_1 @ X28))),
% 0.58/0.78      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.58/0.78  thf('116', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.58/0.78        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.58/0.78           (k1_zfmisc_1 @ 
% 0.58/0.78            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.58/0.78        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78            != (k2_relat_1 @ sk_C))
% 0.58/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['114', '115'])).
% 0.58/0.78  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('118', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['90', '91'])).
% 0.58/0.78  thf('119', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf('120', plain,
% 0.58/0.78      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78         = (k2_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.58/0.78  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('122', plain,
% 0.58/0.78      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.58/0.78         (k1_zfmisc_1 @ 
% 0.58/0.78          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.58/0.78        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.58/0.78      inference('demod', [status(thm)],
% 0.58/0.78                ['116', '117', '118', '119', '120', '121'])).
% 0.58/0.78  thf('123', plain,
% 0.58/0.78      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.58/0.78      inference('simplify', [status(thm)], ['122'])).
% 0.58/0.78  thf('124', plain,
% 0.58/0.78      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.58/0.78         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.58/0.78          | ~ (v2_funct_1 @ X35)
% 0.58/0.78          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.58/0.78          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.58/0.78          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.58/0.78          | ~ (v1_funct_1 @ X35))),
% 0.58/0.78      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.58/0.78  thf('125', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.58/0.78        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.58/0.78             (k2_struct_0 @ sk_A))
% 0.58/0.78        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78            (k4_relat_1 @ sk_C)) = (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 0.58/0.78        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.58/0.78        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78            (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['123', '124'])).
% 0.58/0.78  thf('126', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf(dt_k2_funct_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.78       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.58/0.78         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.58/0.78  thf('127', plain,
% 0.58/0.78      (![X6 : $i]:
% 0.58/0.78         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 0.58/0.78          | ~ (v1_funct_1 @ X6)
% 0.58/0.78          | ~ (v1_relat_1 @ X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.58/0.78  thf('128', plain,
% 0.58/0.78      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.58/0.78        | ~ (v1_relat_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_C))),
% 0.58/0.78      inference('sup+', [status(thm)], ['126', '127'])).
% 0.58/0.78  thf('129', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('131', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.58/0.78  thf('132', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.58/0.78      inference('demod', [status(thm)], ['76', '77'])).
% 0.58/0.78  thf('133', plain,
% 0.58/0.78      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X28)
% 0.58/0.78          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.58/0.78          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 0.58/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.58/0.78          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.58/0.78          | ~ (v1_funct_1 @ X28))),
% 0.58/0.78      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.58/0.78  thf('134', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.58/0.78        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.58/0.78           (k2_struct_0 @ sk_A))
% 0.58/0.78        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78            != (k2_relat_1 @ sk_C))
% 0.58/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['132', '133'])).
% 0.58/0.78  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('136', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['90', '91'])).
% 0.58/0.78  thf('137', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf('138', plain,
% 0.58/0.78      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78         = (k2_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.58/0.78  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('140', plain,
% 0.58/0.78      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.58/0.78         (k2_struct_0 @ sk_A))
% 0.58/0.78        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.58/0.78      inference('demod', [status(thm)],
% 0.58/0.78                ['134', '135', '136', '137', '138', '139'])).
% 0.58/0.78  thf('141', plain,
% 0.58/0.78      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.58/0.78        (k2_struct_0 @ sk_A))),
% 0.58/0.78      inference('simplify', [status(thm)], ['140'])).
% 0.58/0.78  thf('142', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf(t65_funct_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.78       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.58/0.78  thf('143', plain,
% 0.58/0.78      (![X12 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X12)
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.58/0.78          | ~ (v1_funct_1 @ X12)
% 0.58/0.78          | ~ (v1_relat_1 @ X12))),
% 0.58/0.78      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.58/0.78  thf('144', plain,
% 0.58/0.78      ((((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))
% 0.58/0.78        | ~ (v1_relat_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.58/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.58/0.78      inference('sup+', [status(thm)], ['142', '143'])).
% 0.58/0.78  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('148', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.58/0.78  thf('149', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf(t61_funct_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.78       ( ( v2_funct_1 @ A ) =>
% 0.58/0.78         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.58/0.78             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.58/0.78           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.58/0.78             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.78  thf('150', plain,
% 0.58/0.78      (![X11 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X11)
% 0.58/0.78          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 0.58/0.78              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 0.58/0.78          | ~ (v1_funct_1 @ X11)
% 0.58/0.78          | ~ (v1_relat_1 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.58/0.78  thf('151', plain,
% 0.58/0.78      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78          = (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.58/0.78        | ~ (v1_relat_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.58/0.78        | ~ (v2_funct_1 @ sk_C))),
% 0.58/0.78      inference('sup+', [status(thm)], ['149', '150'])).
% 0.58/0.78  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('154', plain, ((v2_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('155', plain,
% 0.58/0.78      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.58/0.78         = (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.58/0.78      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 0.58/0.78  thf(t48_funct_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.78           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.58/0.78               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.58/0.78             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.58/0.78  thf('156', plain,
% 0.58/0.78      (![X9 : $i, X10 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X9)
% 0.58/0.78          | ~ (v1_funct_1 @ X9)
% 0.58/0.78          | (v2_funct_1 @ X9)
% 0.58/0.78          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.58/0.78          | ~ (v2_funct_1 @ (k5_relat_1 @ X9 @ X10))
% 0.58/0.78          | ~ (v1_funct_1 @ X10)
% 0.58/0.78          | ~ (v1_relat_1 @ X10))),
% 0.58/0.78      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.58/0.78  thf('157', plain,
% 0.58/0.78      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.58/0.78        | ~ (v1_relat_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.58/0.78        | ((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.58/0.78        | (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.58/0.78        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.58/0.78        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['155', '156'])).
% 0.58/0.78  thf(fc4_funct_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.58/0.78       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.58/0.78  thf('158', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 0.58/0.78      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.58/0.78  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('161', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf('162', plain,
% 0.58/0.78      (![X12 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X12)
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.58/0.78          | ~ (v1_funct_1 @ X12)
% 0.58/0.78          | ~ (v1_relat_1 @ X12))),
% 0.58/0.78      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.58/0.78  thf('163', plain,
% 0.58/0.78      (![X6 : $i]:
% 0.58/0.78         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.58/0.78          | ~ (v1_funct_1 @ X6)
% 0.58/0.78          | ~ (v1_relat_1 @ X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.58/0.78  thf('164', plain,
% 0.58/0.78      (![X6 : $i]:
% 0.58/0.78         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 0.58/0.78          | ~ (v1_funct_1 @ X6)
% 0.58/0.78          | ~ (v1_relat_1 @ X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.58/0.78  thf('165', plain,
% 0.58/0.78      (![X12 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X12)
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.58/0.78          | ~ (v1_funct_1 @ X12)
% 0.58/0.78          | ~ (v1_relat_1 @ X12))),
% 0.58/0.78      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.58/0.78  thf('166', plain,
% 0.58/0.78      (![X6 : $i]:
% 0.58/0.78         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.58/0.78          | ~ (v1_funct_1 @ X6)
% 0.58/0.78          | ~ (v1_relat_1 @ X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.58/0.78  thf('167', plain,
% 0.58/0.78      (![X6 : $i]:
% 0.58/0.78         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 0.58/0.78          | ~ (v1_funct_1 @ X6)
% 0.58/0.78          | ~ (v1_relat_1 @ X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.58/0.78  thf('168', plain,
% 0.58/0.78      (![X5 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X5)
% 0.58/0.78          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.58/0.78          | ~ (v1_funct_1 @ X5)
% 0.58/0.78          | ~ (v1_relat_1 @ X5))),
% 0.58/0.78      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.58/0.78  thf('169', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.78              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['167', '168'])).
% 0.58/0.78  thf('170', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.78              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['166', '169'])).
% 0.58/0.78  thf('171', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0))),
% 0.58/0.78      inference('simplify', [status(thm)], ['170'])).
% 0.58/0.78  thf('172', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['165', '171'])).
% 0.58/0.78  thf('173', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.58/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ X0))),
% 0.58/0.78      inference('simplify', [status(thm)], ['172'])).
% 0.58/0.78  thf('174', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['164', '173'])).
% 0.58/0.78  thf('175', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.58/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0))),
% 0.58/0.78      inference('simplify', [status(thm)], ['174'])).
% 0.58/0.78  thf('176', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ X0)
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['163', '175'])).
% 0.58/0.78  thf('177', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.58/0.78          | ~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0))),
% 0.58/0.78      inference('simplify', [status(thm)], ['176'])).
% 0.58/0.78  thf('178', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k2_funct_1 @ X0) = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ X0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['162', '177'])).
% 0.58/0.78  thf('179', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ((k2_funct_1 @ X0)
% 0.58/0.78              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.58/0.78      inference('simplify', [status(thm)], ['178'])).
% 0.58/0.78  thf(t37_relat_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( v1_relat_1 @ A ) =>
% 0.58/0.78       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.58/0.78         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.58/0.78  thf('180', plain,
% 0.58/0.78      (![X4 : $i]:
% 0.58/0.78         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.58/0.78          | ~ (v1_relat_1 @ X4))),
% 0.58/0.78      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.58/0.78  thf('181', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['179', '180'])).
% 0.58/0.78  thf('182', plain,
% 0.58/0.78      ((~ (v1_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 0.58/0.78        | ~ (v2_funct_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.58/0.78        | ~ (v1_relat_1 @ sk_C)
% 0.58/0.78        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.58/0.78            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['161', '181'])).
% 0.58/0.78  thf('183', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.58/0.78  thf('184', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('188', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf('189', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.58/0.78  thf('190', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf('191', plain,
% 0.58/0.78      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.58/0.78      inference('demod', [status(thm)],
% 0.58/0.78                ['182', '183', '184', '185', '186', '187', '188', '189', '190'])).
% 0.58/0.78  thf('192', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.58/0.78  thf('193', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.58/0.78  thf('194', plain,
% 0.58/0.78      (![X6 : $i]:
% 0.58/0.78         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.58/0.78          | ~ (v1_funct_1 @ X6)
% 0.58/0.78          | ~ (v1_relat_1 @ X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.58/0.78  thf('195', plain,
% 0.58/0.78      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.58/0.78        | ~ (v1_relat_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_C))),
% 0.58/0.78      inference('sup+', [status(thm)], ['193', '194'])).
% 0.58/0.78  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('198', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['195', '196', '197'])).
% 0.58/0.78  thf('199', plain,
% 0.58/0.78      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.58/0.78        | (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.58/0.78      inference('demod', [status(thm)],
% 0.58/0.78                ['157', '158', '159', '160', '191', '192', '198'])).
% 0.58/0.78  thf('200', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.58/0.78      inference('simplify', [status(thm)], ['199'])).
% 0.58/0.78  thf('201', plain,
% 0.58/0.78      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.58/0.78      inference('simplify', [status(thm)], ['122'])).
% 0.58/0.78  thf('202', plain,
% 0.58/0.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.78         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.58/0.78          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.58/0.78  thf('203', plain,
% 0.58/0.78      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['201', '202'])).
% 0.58/0.78  thf('204', plain,
% 0.58/0.78      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.58/0.78      inference('demod', [status(thm)],
% 0.58/0.78                ['182', '183', '184', '185', '186', '187', '188', '189', '190'])).
% 0.58/0.78  thf('205', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['56', '57', '64'])).
% 0.58/0.78  thf('206', plain,
% 0.58/0.78      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.58/0.78      inference('demod', [status(thm)], ['204', '205'])).
% 0.58/0.78  thf('207', plain,
% 0.58/0.78      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78         (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['203', '206'])).
% 0.58/0.78  thf('208', plain,
% 0.58/0.78      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78          (k4_relat_1 @ sk_C)) = (sk_C))
% 0.58/0.78        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)],
% 0.58/0.78                ['125', '131', '141', '148', '200', '207'])).
% 0.58/0.78  thf('209', plain,
% 0.58/0.78      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.78         (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.58/0.78      inference('simplify', [status(thm)], ['208'])).
% 0.58/0.78  thf('210', plain,
% 0.58/0.78      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.58/0.78          sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['71', '113', '209'])).
% 0.58/0.78  thf('211', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['60', '61'])).
% 0.58/0.78  thf('212', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_C @ 
% 0.58/0.78        (k1_zfmisc_1 @ 
% 0.58/0.78         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['60', '61'])).
% 0.58/0.78  thf(reflexivity_r2_funct_2, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.78         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.78       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.58/0.78  thf('213', plain,
% 0.58/0.78      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.78         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 0.58/0.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.58/0.78          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.58/0.78          | ~ (v1_funct_1 @ X26)
% 0.58/0.78          | ~ (v1_funct_1 @ X27)
% 0.58/0.78          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 0.58/0.78          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.58/0.78      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.58/0.78  thf('214', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X0 @ 
% 0.58/0.78             (k1_zfmisc_1 @ 
% 0.58/0.78              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.58/0.78          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ sk_C)
% 0.58/0.78          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.78          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.58/0.78             sk_C))),
% 0.58/0.78      inference('sup-', [status(thm)], ['212', '213'])).
% 0.58/0.78  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('216', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['85', '86'])).
% 0.58/0.78  thf('217', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X0 @ 
% 0.58/0.78             (k1_zfmisc_1 @ 
% 0.58/0.78              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.58/0.78          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.58/0.78             sk_C))),
% 0.58/0.78      inference('demod', [status(thm)], ['214', '215', '216'])).
% 0.58/0.78  thf('218', plain,
% 0.58/0.78      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_C)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['211', '217'])).
% 0.58/0.78  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('220', plain,
% 0.58/0.78      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['85', '86'])).
% 0.58/0.78  thf('221', plain,
% 0.58/0.78      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.58/0.78      inference('demod', [status(thm)], ['218', '219', '220'])).
% 0.58/0.78  thf('222', plain, ($false), inference('demod', [status(thm)], ['210', '221'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
