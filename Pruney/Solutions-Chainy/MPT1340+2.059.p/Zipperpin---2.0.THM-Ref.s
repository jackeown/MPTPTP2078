%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GTc8GQubrl

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:16 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  271 (1080 expanded)
%              Number of leaves         :   44 ( 336 expanded)
%              Depth                    :   36
%              Number of atoms          : 2595 (22883 expanded)
%              Number of equality atoms :  135 ( 651 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','18','21'])).

thf('23',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','35'])).

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','42'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('44',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('45',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','49'])).

thf('51',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('52',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('58',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','56','57'])).

thf('59',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

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

thf('61',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X32 @ X34 )
       != X32 )
      | ~ ( v2_funct_1 @ X34 )
      | ( ( k2_tops_2 @ X33 @ X32 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','70'])).

thf('72',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('77',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X32 @ X34 )
       != X32 )
      | ~ ( v2_funct_1 @ X34 )
      | ( ( k2_tops_2 @ X33 @ X32 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('91',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('94',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('102',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('107',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','104','109','110'])).

thf('112',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('115',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X27 ) @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('119',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('127',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('128',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('129',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('130',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('131',plain,(
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

thf('132',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('133',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('134',plain,(
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
    inference('sup-',[status(thm)],['132','133'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('135',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('136',plain,(
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
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
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
    inference('sup-',[status(thm)],['131','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
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
    inference('sup-',[status(thm)],['129','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('145',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('148',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('149',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('150',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('151',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
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
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','158'])).

thf('160',plain,(
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
    inference('sup-',[status(thm)],['145','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['144','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['143','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['167','168','169','170'])).

thf('172',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['128','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('174',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('175',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','177','178','179','180'])).

thf('182',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('183',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('188',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('189',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','184','185','186','187','188'])).

thf('190',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','193'])).

thf('195',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195','196','197','198'])).

thf('200',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','112','125','200'])).

thf('202',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('203',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('204',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['201','204'])).

thf('206',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['76','205'])).

thf('207',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('208',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['206','207','208','209','210'])).

thf('212',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['58','75','212'])).

thf('214',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','213'])).

thf('215',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

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

thf('216',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_funct_2 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('217',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['215','217'])).

thf('219',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('223',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    $false ),
    inference(demod,[status(thm)],['214','221','222','223','224'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GTc8GQubrl
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:33:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 410 iterations in 0.173s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.64  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.64  thf(t65_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      (![X11 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X11)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 0.45/0.64          | ~ (v1_funct_1 @ X11)
% 0.45/0.64          | ~ (v1_relat_1 @ X11))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf(d3_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf(t64_tops_2, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.64                 ( m1_subset_1 @
% 0.45/0.64                   C @ 
% 0.45/0.64                   ( k1_zfmisc_1 @
% 0.45/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.64               ( ( ( ( k2_relset_1 @
% 0.45/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.64                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.64                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.64                 ( r2_funct_2 @
% 0.45/0.64                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.64                   ( k2_tops_2 @
% 0.45/0.64                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.64                     ( k2_tops_2 @
% 0.45/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.64                   C ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( l1_struct_0 @ A ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.64              ( ![C:$i]:
% 0.45/0.64                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.64                    ( v1_funct_2 @
% 0.45/0.64                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.64                    ( m1_subset_1 @
% 0.45/0.64                      C @ 
% 0.45/0.64                      ( k1_zfmisc_1 @
% 0.45/0.64                        ( k2_zfmisc_1 @
% 0.45/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.64                  ( ( ( ( k2_relset_1 @
% 0.45/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.64                        ( k2_struct_0 @ B ) ) & 
% 0.45/0.64                      ( v2_funct_1 @ C ) ) =>
% 0.45/0.64                    ( r2_funct_2 @
% 0.45/0.64                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.64                      ( k2_tops_2 @
% 0.45/0.64                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.64                        ( k2_tops_2 @
% 0.45/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.64                      C ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc5_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.64       ( ![C:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.64             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.45/0.64          | (v1_partfun1 @ X18 @ X19)
% 0.45/0.64          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.45/0.64          | ~ (v1_funct_1 @ X18)
% 0.45/0.64          | (v1_xboole_0 @ X20))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.64  thf(d4_partfun1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.64       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X22 @ X21)
% 0.45/0.64          | ((k1_relat_1 @ X22) = (X21))
% 0.45/0.64          | ~ (v4_relat_1 @ X22 @ X21)
% 0.45/0.64          | ~ (v1_relat_1 @ X22))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc2_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ 
% 0.45/0.64           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.64        | (v1_relat_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf(fc6_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.64  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X12 @ X13)
% 0.45/0.64          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('21', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['13', '18', '21'])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['23', '24'])).
% 0.45/0.64  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.45/0.64          | (v1_partfun1 @ X18 @ X19)
% 0.45/0.64          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.45/0.64          | ~ (v1_funct_1 @ X18)
% 0.45/0.64          | (v1_xboole_0 @ X20))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.64  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['31', '32'])).
% 0.45/0.64  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['29', '30', '35'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X22 @ X21)
% 0.45/0.64          | ((k1_relat_1 @ X22) = (X21))
% 0.45/0.64          | ~ (v4_relat_1 @ X22 @ X21)
% 0.45/0.64          | ~ (v1_relat_1 @ X22))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.64  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X12 @ X13)
% 0.45/0.64          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('42', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['38', '39', '42'])).
% 0.45/0.64  thf(fc2_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.64       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (![X31 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X31))
% 0.45/0.64          | ~ (l1_struct_0 @ X31)
% 0.45/0.64          | (v2_struct_0 @ X31))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.45/0.64        | (v2_struct_0 @ sk_B)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.64  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('49', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '49'])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X31 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X31))
% 0.45/0.64          | ~ (l1_struct_0 @ X31)
% 0.45/0.64          | (v2_struct_0 @ X31))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.45/0.64        | (v2_struct_0 @ sk_B)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('53', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.64  thf('55', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('56', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['54', '55'])).
% 0.45/0.64  thf('57', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['54', '55'])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '56', '57'])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('60', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf(d4_tops_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.64         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.64  thf('61', plain,
% 0.45/0.64      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X33 @ X32 @ X34) != (X32))
% 0.45/0.64          | ~ (v2_funct_1 @ X34)
% 0.45/0.64          | ((k2_tops_2 @ X33 @ X32 @ X34) = (k2_funct_1 @ X34))
% 0.45/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.45/0.64          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.45/0.64          | ~ (v1_funct_1 @ X34))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.64  thf('62', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            != (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.64  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('64', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('68', plain,
% 0.45/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['66', '67'])).
% 0.45/0.64  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.64  thf('71', plain,
% 0.45/0.64      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['62', '63', '64', '65', '70'])).
% 0.45/0.64  thf('72', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['59', '71'])).
% 0.45/0.64  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('74', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['72', '73'])).
% 0.45/0.64  thf('75', plain,
% 0.45/0.64      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['74'])).
% 0.45/0.64  thf(t55_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v2_funct_1 @ A ) =>
% 0.45/0.64         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.64           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('76', plain,
% 0.45/0.64      (![X9 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X9)
% 0.45/0.64          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.45/0.64          | ~ (v1_funct_1 @ X9)
% 0.45/0.64          | ~ (v1_relat_1 @ X9))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('77', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('78', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf(t31_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.64         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.64           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.64           ( m1_subset_1 @
% 0.45/0.64             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('79', plain,
% 0.45/0.64      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X27)
% 0.45/0.64          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.45/0.64          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.45/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.45/0.64          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.45/0.64          | ~ (v1_funct_1 @ X27))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('80', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64           (k1_zfmisc_1 @ 
% 0.45/0.64            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            != (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.64  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('82', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('83', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.64  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('85', plain,
% 0.45/0.64      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.45/0.64        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.45/0.64  thf('86', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.64        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64           (k1_zfmisc_1 @ 
% 0.45/0.64            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['77', '85'])).
% 0.45/0.64  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('88', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.64        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64           (k1_zfmisc_1 @ 
% 0.45/0.64            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['86', '87'])).
% 0.45/0.64  thf('89', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['88'])).
% 0.45/0.64  thf('90', plain,
% 0.45/0.64      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X33 @ X32 @ X34) != (X32))
% 0.45/0.64          | ~ (v2_funct_1 @ X34)
% 0.45/0.64          | ((k2_tops_2 @ X33 @ X32 @ X34) = (k2_funct_1 @ X34))
% 0.45/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.45/0.64          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.45/0.64          | ~ (v1_funct_1 @ X34))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.64  thf('91', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64             (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['89', '90'])).
% 0.45/0.64  thf('92', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('93', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('94', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['92', '93'])).
% 0.45/0.64  thf('95', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('96', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['94', '95'])).
% 0.45/0.64  thf('97', plain,
% 0.45/0.64      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X27)
% 0.45/0.64          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.45/0.64          | (v1_funct_1 @ (k2_funct_1 @ X27))
% 0.45/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.45/0.64          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.45/0.64          | ~ (v1_funct_1 @ X27))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('98', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            != (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['96', '97'])).
% 0.45/0.64  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('100', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('101', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('102', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['100', '101'])).
% 0.45/0.64  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('104', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.64  thf('105', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('106', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.64  thf('107', plain,
% 0.45/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['105', '106'])).
% 0.45/0.64  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('109', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['107', '108'])).
% 0.45/0.64  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('111', plain,
% 0.45/0.64      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['98', '99', '104', '109', '110'])).
% 0.45/0.64  thf('112', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['111'])).
% 0.45/0.64  thf('113', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('114', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('115', plain,
% 0.45/0.64      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X27)
% 0.45/0.64          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.45/0.64          | (v1_funct_2 @ (k2_funct_1 @ X27) @ X28 @ X29)
% 0.45/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.45/0.64          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.45/0.64          | ~ (v1_funct_1 @ X27))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('116', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            != (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['114', '115'])).
% 0.45/0.64  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('118', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('119', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.64  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('121', plain,
% 0.45/0.64      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64         (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 0.45/0.64  thf('122', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['113', '121'])).
% 0.45/0.64  thf('123', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('124', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['122', '123'])).
% 0.45/0.64  thf('125', plain,
% 0.45/0.64      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64        (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('simplify', [status(thm)], ['124'])).
% 0.45/0.64  thf('126', plain,
% 0.45/0.64      (![X9 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X9)
% 0.45/0.64          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.45/0.64          | ~ (v1_funct_1 @ X9)
% 0.50/0.64          | ~ (v1_relat_1 @ X9))),
% 0.50/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.50/0.64  thf(dt_k2_funct_1, axiom,
% 0.50/0.64    (![A:$i]:
% 0.50/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.64       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.50/0.64         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.50/0.64  thf('127', plain,
% 0.50/0.64      (![X4 : $i]:
% 0.50/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.50/0.64          | ~ (v1_funct_1 @ X4)
% 0.50/0.64          | ~ (v1_relat_1 @ X4))),
% 0.50/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.64  thf('128', plain,
% 0.50/0.64      (![X11 : $i]:
% 0.50/0.64         (~ (v2_funct_1 @ X11)
% 0.50/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 0.50/0.64          | ~ (v1_funct_1 @ X11)
% 0.50/0.64          | ~ (v1_relat_1 @ X11))),
% 0.50/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.64  thf('129', plain,
% 0.50/0.64      (![X9 : $i]:
% 0.50/0.64         (~ (v2_funct_1 @ X9)
% 0.50/0.64          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.50/0.64          | ~ (v1_funct_1 @ X9)
% 0.50/0.64          | ~ (v1_relat_1 @ X9))),
% 0.50/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.50/0.64  thf('130', plain,
% 0.50/0.64      (![X4 : $i]:
% 0.50/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.50/0.64          | ~ (v1_funct_1 @ X4)
% 0.50/0.64          | ~ (v1_relat_1 @ X4))),
% 0.50/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.64  thf('131', plain,
% 0.50/0.64      (![X4 : $i]:
% 0.50/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.50/0.64          | ~ (v1_funct_1 @ X4)
% 0.50/0.64          | ~ (v1_relat_1 @ X4))),
% 0.50/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.64  thf(t61_funct_1, axiom,
% 0.50/0.64    (![A:$i]:
% 0.50/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.64       ( ( v2_funct_1 @ A ) =>
% 0.50/0.64         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.50/0.64             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.50/0.64           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.50/0.64             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.50/0.64  thf('132', plain,
% 0.50/0.64      (![X10 : $i]:
% 0.50/0.64         (~ (v2_funct_1 @ X10)
% 0.50/0.64          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.50/0.64              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.50/0.64          | ~ (v1_funct_1 @ X10)
% 0.50/0.64          | ~ (v1_relat_1 @ X10))),
% 0.50/0.64      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.50/0.64  thf(t48_funct_1, axiom,
% 0.50/0.64    (![A:$i]:
% 0.50/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.64       ( ![B:$i]:
% 0.50/0.64         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.64           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.50/0.64               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.50/0.64             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.50/0.64  thf('133', plain,
% 0.50/0.64      (![X7 : $i, X8 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ X7)
% 0.50/0.64          | ~ (v1_funct_1 @ X7)
% 0.50/0.64          | (v2_funct_1 @ X7)
% 0.50/0.64          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.50/0.64          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.50/0.64          | ~ (v1_funct_1 @ X8)
% 0.50/0.64          | ~ (v1_relat_1 @ X8))),
% 0.50/0.64      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.50/0.64  thf('134', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.50/0.64          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.64      inference('sup-', [status(thm)], ['132', '133'])).
% 0.50/0.64  thf(fc4_funct_1, axiom,
% 0.50/0.64    (![A:$i]:
% 0.50/0.64     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.50/0.64       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.50/0.64  thf('135', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.50/0.64      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.50/0.64  thf('136', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.50/0.64          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.64      inference('demod', [status(thm)], ['134', '135'])).
% 0.50/0.64  thf('137', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0))),
% 0.50/0.64      inference('simplify', [status(thm)], ['136'])).
% 0.50/0.64  thf('138', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.50/0.64          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.64      inference('sup-', [status(thm)], ['131', '137'])).
% 0.50/0.64  thf('139', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0))),
% 0.50/0.64      inference('simplify', [status(thm)], ['138'])).
% 0.50/0.64  thf('140', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.50/0.64          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.64      inference('sup-', [status(thm)], ['130', '139'])).
% 0.50/0.64  thf('141', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0))),
% 0.50/0.64      inference('simplify', [status(thm)], ['140'])).
% 0.50/0.64  thf('142', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.64      inference('sup-', [status(thm)], ['129', '141'])).
% 0.50/0.64  thf('143', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0))),
% 0.50/0.64      inference('simplify', [status(thm)], ['142'])).
% 0.50/0.64  thf('144', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.64      inference('simplify', [status(thm)], ['111'])).
% 0.50/0.64  thf('145', plain,
% 0.50/0.64      (![X4 : $i]:
% 0.50/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.50/0.64          | ~ (v1_funct_1 @ X4)
% 0.50/0.64          | ~ (v1_relat_1 @ X4))),
% 0.50/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.64  thf('146', plain,
% 0.50/0.64      (![X11 : $i]:
% 0.50/0.64         (~ (v2_funct_1 @ X11)
% 0.50/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 0.50/0.64          | ~ (v1_funct_1 @ X11)
% 0.50/0.64          | ~ (v1_relat_1 @ X11))),
% 0.50/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.64  thf('147', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0))),
% 0.50/0.64      inference('simplify', [status(thm)], ['142'])).
% 0.50/0.64  thf('148', plain,
% 0.50/0.64      (![X4 : $i]:
% 0.50/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.50/0.64          | ~ (v1_funct_1 @ X4)
% 0.50/0.64          | ~ (v1_relat_1 @ X4))),
% 0.50/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.64  thf('149', plain,
% 0.50/0.64      (![X4 : $i]:
% 0.50/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.50/0.64          | ~ (v1_funct_1 @ X4)
% 0.50/0.64          | ~ (v1_relat_1 @ X4))),
% 0.50/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.64  thf('150', plain,
% 0.50/0.64      (![X11 : $i]:
% 0.50/0.64         (~ (v2_funct_1 @ X11)
% 0.50/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 0.50/0.64          | ~ (v1_funct_1 @ X11)
% 0.50/0.64          | ~ (v1_relat_1 @ X11))),
% 0.50/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.64  thf('151', plain,
% 0.50/0.64      (![X10 : $i]:
% 0.50/0.64         (~ (v2_funct_1 @ X10)
% 0.50/0.64          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.50/0.64              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.50/0.64          | ~ (v1_funct_1 @ X10)
% 0.50/0.64          | ~ (v1_relat_1 @ X10))),
% 0.50/0.64      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.50/0.64  thf('152', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.50/0.64            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.64      inference('sup+', [status(thm)], ['150', '151'])).
% 0.50/0.64  thf('153', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.50/0.64              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.50/0.64      inference('sup-', [status(thm)], ['149', '152'])).
% 0.50/0.64  thf('154', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.50/0.64            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0))),
% 0.50/0.64      inference('simplify', [status(thm)], ['153'])).
% 0.50/0.64  thf('155', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.50/0.64              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.50/0.64      inference('sup-', [status(thm)], ['148', '154'])).
% 0.50/0.64  thf('156', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.50/0.64            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0))),
% 0.50/0.64      inference('simplify', [status(thm)], ['155'])).
% 0.50/0.64  thf('157', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.50/0.64              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.50/0.64      inference('sup-', [status(thm)], ['147', '156'])).
% 0.50/0.64  thf('158', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.50/0.64            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0))),
% 0.50/0.64      inference('simplify', [status(thm)], ['157'])).
% 0.50/0.64  thf('159', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.50/0.64            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.64      inference('sup+', [status(thm)], ['146', '158'])).
% 0.50/0.64  thf('160', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0)
% 0.50/0.64          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.50/0.64              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.50/0.64      inference('sup-', [status(thm)], ['145', '159'])).
% 0.50/0.64  thf('161', plain,
% 0.50/0.64      (![X0 : $i]:
% 0.50/0.64         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.50/0.64            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.50/0.64          | ~ (v2_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.64          | ~ (v1_funct_1 @ X0)
% 0.50/0.64          | ~ (v1_relat_1 @ X0))),
% 0.50/0.64      inference('simplify', [status(thm)], ['160'])).
% 0.50/0.64  thf('162', plain,
% 0.50/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.64        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.50/0.64            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.50/0.64      inference('sup-', [status(thm)], ['144', '161'])).
% 0.50/0.64  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.64  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('166', plain,
% 0.50/0.64      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.64        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.50/0.64            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.50/0.64      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 0.50/0.64  thf('167', plain,
% 0.50/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.64        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.50/0.64            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.50/0.64      inference('sup-', [status(thm)], ['143', '166'])).
% 0.50/0.64  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.64  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('171', plain,
% 0.50/0.64      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.50/0.64         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.50/0.64      inference('demod', [status(thm)], ['167', '168', '169', '170'])).
% 0.50/0.64  thf('172', plain,
% 0.50/0.64      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.50/0.64          = (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.50/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.64      inference('sup+', [status(thm)], ['128', '171'])).
% 0.50/0.64  thf('173', plain,
% 0.50/0.64      ((m1_subset_1 @ sk_C @ 
% 0.50/0.64        (k1_zfmisc_1 @ 
% 0.50/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.50/0.64    (![A:$i,B:$i,C:$i]:
% 0.50/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.50/0.64  thf('174', plain,
% 0.50/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.64         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.50/0.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.50/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.50/0.64  thf('175', plain,
% 0.50/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.50/0.64         = (k2_relat_1 @ sk_C))),
% 0.50/0.64      inference('sup-', [status(thm)], ['173', '174'])).
% 0.50/0.64  thf('176', plain,
% 0.50/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.50/0.64         = (k2_struct_0 @ sk_B))),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('177', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.64      inference('sup+', [status(thm)], ['175', '176'])).
% 0.50/0.64  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.64  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('181', plain,
% 0.50/0.64      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.50/0.64         = (k6_relat_1 @ (k2_struct_0 @ sk_B)))),
% 0.50/0.64      inference('demod', [status(thm)], ['172', '177', '178', '179', '180'])).
% 0.50/0.64  thf('182', plain,
% 0.50/0.64      (![X7 : $i, X8 : $i]:
% 0.50/0.64         (~ (v1_relat_1 @ X7)
% 0.50/0.64          | ~ (v1_funct_1 @ X7)
% 0.50/0.64          | (v2_funct_1 @ X7)
% 0.50/0.64          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.50/0.64          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.50/0.64          | ~ (v1_funct_1 @ X8)
% 0.50/0.64          | ~ (v1_relat_1 @ X8))),
% 0.50/0.64      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.50/0.64  thf('183', plain,
% 0.50/0.64      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_struct_0 @ sk_B)))
% 0.50/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.64        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.50/0.64        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.64      inference('sup-', [status(thm)], ['181', '182'])).
% 0.50/0.64  thf('184', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.50/0.64      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.50/0.64  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.64  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('187', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.50/0.64      inference('clc', [status(thm)], ['47', '48'])).
% 0.50/0.64  thf('188', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.64      inference('simplify', [status(thm)], ['111'])).
% 0.50/0.64  thf('189', plain,
% 0.50/0.64      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.50/0.64        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.64      inference('demod', [status(thm)],
% 0.50/0.64                ['183', '184', '185', '186', '187', '188'])).
% 0.50/0.64  thf('190', plain,
% 0.50/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.64        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.64        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.50/0.64      inference('sup-', [status(thm)], ['127', '189'])).
% 0.50/0.64  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.64  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('193', plain,
% 0.50/0.64      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.64        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.50/0.64      inference('demod', [status(thm)], ['190', '191', '192'])).
% 0.50/0.64  thf('194', plain,
% 0.50/0.64      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.50/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.64        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.64      inference('sup-', [status(thm)], ['126', '193'])).
% 0.50/0.64  thf('195', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.50/0.64      inference('clc', [status(thm)], ['47', '48'])).
% 0.50/0.64  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.64  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('198', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('199', plain,
% 0.50/0.64      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.50/0.64        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.64      inference('demod', [status(thm)], ['194', '195', '196', '197', '198'])).
% 0.50/0.64  thf('200', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.64      inference('simplify', [status(thm)], ['199'])).
% 0.50/0.64  thf('201', plain,
% 0.50/0.64      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.64          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.50/0.64        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.64            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.50/0.64      inference('demod', [status(thm)], ['91', '112', '125', '200'])).
% 0.50/0.64  thf('202', plain,
% 0.50/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.64        (k1_zfmisc_1 @ 
% 0.50/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.50/0.64      inference('simplify', [status(thm)], ['88'])).
% 0.50/0.64  thf('203', plain,
% 0.50/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.64         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.50/0.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.50/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.50/0.64  thf('204', plain,
% 0.50/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.64         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.64      inference('sup-', [status(thm)], ['202', '203'])).
% 0.50/0.64  thf('205', plain,
% 0.50/0.64      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.64          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.50/0.64        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.50/0.64      inference('demod', [status(thm)], ['201', '204'])).
% 0.50/0.64  thf('206', plain,
% 0.50/0.64      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.50/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.64        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.64      inference('sup-', [status(thm)], ['76', '205'])).
% 0.50/0.64  thf('207', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.50/0.64      inference('clc', [status(thm)], ['47', '48'])).
% 0.50/0.64  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.64  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('210', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('211', plain,
% 0.50/0.64      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.50/0.64        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.64      inference('demod', [status(thm)], ['206', '207', '208', '209', '210'])).
% 0.50/0.64  thf('212', plain,
% 0.50/0.64      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.64         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.64      inference('simplify', [status(thm)], ['211'])).
% 0.50/0.64  thf('213', plain,
% 0.50/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.64          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['58', '75', '212'])).
% 0.50/0.64  thf('214', plain,
% 0.50/0.64      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.50/0.64           sk_C)
% 0.50/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.64      inference('sup-', [status(thm)], ['0', '213'])).
% 0.50/0.64  thf('215', plain,
% 0.50/0.64      ((m1_subset_1 @ sk_C @ 
% 0.50/0.64        (k1_zfmisc_1 @ 
% 0.50/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.50/0.64  thf(redefinition_r2_funct_2, axiom,
% 0.50/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.50/0.64         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.64       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.50/0.64  thf('216', plain,
% 0.50/0.64      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.50/0.64         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.50/0.64          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.50/0.64          | ~ (v1_funct_1 @ X23)
% 0.50/0.64          | ~ (v1_funct_1 @ X26)
% 0.50/0.64          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.50/0.64          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.50/0.64          | (r2_funct_2 @ X24 @ X25 @ X23 @ X26)
% 0.50/0.64          | ((X23) != (X26)))),
% 0.50/0.64      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.50/0.64  thf('217', plain,
% 0.50/0.64      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.50/0.64         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 0.50/0.64          | ~ (v1_funct_1 @ X26)
% 0.50/0.64          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.50/0.64          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.50/0.64      inference('simplify', [status(thm)], ['216'])).
% 0.50/0.64  thf('218', plain,
% 0.50/0.64      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.64        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.50/0.64           sk_C))),
% 0.50/0.64      inference('sup-', [status(thm)], ['215', '217'])).
% 0.50/0.64  thf('219', plain,
% 0.50/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.50/0.64  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('221', plain,
% 0.50/0.64      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['218', '219', '220'])).
% 0.50/0.64  thf('222', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.50/0.64  thf('223', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('224', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.64  thf('225', plain, ($false),
% 0.50/0.64      inference('demod', [status(thm)], ['214', '221', '222', '223', '224'])).
% 0.50/0.64  
% 0.50/0.64  % SZS output end Refutation
% 0.50/0.64  
% 0.50/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
