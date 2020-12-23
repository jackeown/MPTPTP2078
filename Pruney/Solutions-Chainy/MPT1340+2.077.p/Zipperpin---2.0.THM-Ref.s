%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MJQuRREAVM

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:20 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  340 (11164 expanded)
%              Number of leaves         :   43 (3247 expanded)
%              Depth                    :   37
%              Number of atoms          : 3222 (248225 expanded)
%              Number of equality atoms :  149 (7388 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','8','9'])).

thf('11',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('48',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('50',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('56',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','62'])).

thf('64',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','63'])).

thf('65',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','63'])).

thf('66',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','63'])).

thf('67',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','64','65','66'])).

thf('68',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

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
    inference('sup+',[status(thm)],['6','7'])).

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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X31 @ X33 )
       != X31 )
      | ~ ( v2_funct_1 @ X33 )
      | ( ( k2_tops_2 @ X32 @ X31 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
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
    inference('sup+',[status(thm)],['6','7'])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['94','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','92','93','105'])).

thf('107',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['71','107'])).

thf('109',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

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

thf('111',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('116',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','117','118'])).

thf('120',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['109','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('122',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X31 @ X33 )
       != X31 )
      | ~ ( v2_funct_1 @ X33 )
      | ( ( k2_tops_2 @ X32 @ X31 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('126',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('128',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('129',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('132',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133'])).

thf('135',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('138',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X26 ) @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('142',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('143',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','144'])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('147',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['148'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('150',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('152',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('153',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('156',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('157',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157'])).

thf('159',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('163',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','162'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('164',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('165',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('166',plain,(
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
    inference('sup-',[status(thm)],['164','165'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('167',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('168',plain,(
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
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','62'])).

thf('175',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('176',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['170','171','172','173','174','175'])).

thf('177',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','176'])).

thf('178',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','62'])).

thf('179',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['177','178','179','180','181'])).

thf('183',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','135','149','183'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('185',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('186',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('187',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('188',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('190',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['148'])).

thf('191',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['182'])).

thf('192',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('194',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('195',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('197',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('198',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('199',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['182'])).

thf('200',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('201',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('202',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('203',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('204',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != X20 )
      | ( v1_partfun1 @ X21 @ X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('205',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v4_relat_1 @ X21 @ ( k1_relat_1 @ X21 ) )
      | ( v1_partfun1 @ X21 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['203','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['202','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['201','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['200','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['199','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('214',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','62'])).

thf('217',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('218',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('219',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('220',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['212','213','214','215','216','217','218','219'])).

thf('221',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['198','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('223',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['221','222','223','224'])).

thf('226',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['197','225'])).

thf('227',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('228',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('229',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['182'])).

thf('230',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['226','227','228','229'])).

thf('231',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('232',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('234',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','62'])).

thf('235',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['196','235'])).

thf('237',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','62'])).

thf('238',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('239',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('240',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237','238','239','240','241'])).

thf('243',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','242'])).

thf('244',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['192','243'])).

thf('245',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

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

thf('247',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_funct_2 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['248','249','250'])).

thf('252',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['245','251'])).

thf('253',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('254',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('255',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('257',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['148'])).

thf('258',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['182'])).

thf('259',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['255','256','257','258'])).

thf('260',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','242'])).

thf('261',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('262',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('264',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X26 ) @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('265',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('267',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['148'])).

thf('268',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['182'])).

thf('269',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['265','266','267','268'])).

thf('270',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','242'])).

thf('271',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['269','270'])).

thf('272',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['252','262','272'])).

thf('274',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['185','273'])).

thf('275',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('276',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_funct_2 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('277',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_funct_2 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['275','277'])).

thf('279',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('280',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['278','279','280'])).

thf('282',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('283',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['274','281','282','283','284'])).

thf('286',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','242'])).

thf('287',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['184','285','286'])).

thf('288',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('290',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_funct_2 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('291',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('293',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['291','292','293'])).

thf('295',plain,(
    $false ),
    inference(demod,[status(thm)],['108','288','294'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MJQuRREAVM
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 430 iterations in 0.224s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.49/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.49/0.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.49/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.68  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.49/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.49/0.68  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.49/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.49/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.49/0.68  thf(d3_struct_0, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.49/0.68  thf('0', plain,
% 0.49/0.68      (![X29 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf('1', plain,
% 0.49/0.68      (![X29 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf(t64_tops_2, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_struct_0 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.49/0.68           ( ![C:$i]:
% 0.49/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.49/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.68                 ( m1_subset_1 @
% 0.49/0.68                   C @ 
% 0.49/0.68                   ( k1_zfmisc_1 @
% 0.49/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.68               ( ( ( ( k2_relset_1 @
% 0.49/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.49/0.68                     ( k2_struct_0 @ B ) ) & 
% 0.49/0.68                   ( v2_funct_1 @ C ) ) =>
% 0.49/0.68                 ( r2_funct_2 @
% 0.49/0.68                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.49/0.68                   ( k2_tops_2 @
% 0.49/0.68                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.49/0.68                     ( k2_tops_2 @
% 0.49/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.49/0.68                   C ) ) ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( l1_struct_0 @ A ) =>
% 0.49/0.68          ( ![B:$i]:
% 0.49/0.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.49/0.68              ( ![C:$i]:
% 0.49/0.68                ( ( ( v1_funct_1 @ C ) & 
% 0.49/0.68                    ( v1_funct_2 @
% 0.49/0.68                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.68                    ( m1_subset_1 @
% 0.49/0.68                      C @ 
% 0.49/0.68                      ( k1_zfmisc_1 @
% 0.49/0.68                        ( k2_zfmisc_1 @
% 0.49/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.68                  ( ( ( ( k2_relset_1 @
% 0.49/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.49/0.68                        ( k2_struct_0 @ B ) ) & 
% 0.49/0.68                      ( v2_funct_1 @ C ) ) =>
% 0.49/0.68                    ( r2_funct_2 @
% 0.49/0.68                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.49/0.68                      ( k2_tops_2 @
% 0.49/0.68                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.49/0.68                        ( k2_tops_2 @
% 0.49/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.49/0.68                      C ) ) ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.68          sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.68           sk_C)
% 0.49/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.68  thf('4', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.49/0.68  thf('5', plain,
% 0.49/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.68         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.49/0.68          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.68         = (k2_relat_1 @ sk_C))),
% 0.49/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.68         = (k2_struct_0 @ sk_B))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('8', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.68  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ 
% 0.49/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.68          sk_C)),
% 0.49/0.68      inference('demod', [status(thm)], ['3', '8', '9'])).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (![X29 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf('12', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      (((m1_subset_1 @ sk_C @ 
% 0.49/0.68         (k1_zfmisc_1 @ 
% 0.49/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.49/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.49/0.68  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.49/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.49/0.68  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.68      inference('demod', [status(thm)], ['15', '16'])).
% 0.49/0.68  thf(cc5_funct_2, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.49/0.68       ( ![C:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.49/0.68             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.49/0.68          | (v1_partfun1 @ X17 @ X18)
% 0.49/0.68          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.49/0.68          | ~ (v1_funct_1 @ X17)
% 0.49/0.68          | (v1_xboole_0 @ X19))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.49/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.49/0.68        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.68  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      (![X29 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.49/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['21', '22'])).
% 0.49/0.68  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['25', '26'])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.49/0.68        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['19', '20', '27'])).
% 0.49/0.68  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.68  thf(fc5_struct_0, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.49/0.68       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      (![X30 : $i]:
% 0.49/0.68         (~ (v1_xboole_0 @ (k2_struct_0 @ X30))
% 0.49/0.68          | ~ (l1_struct_0 @ X30)
% 0.49/0.68          | (v2_struct_0 @ X30))),
% 0.49/0.68      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.49/0.68        | (v2_struct_0 @ sk_B)
% 0.49/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.49/0.68  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['31', '32'])).
% 0.49/0.68  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('35', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.49/0.68      inference('clc', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('36', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['28', '35'])).
% 0.49/0.68  thf(d4_partfun1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.49/0.68       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (![X20 : $i, X21 : $i]:
% 0.49/0.68         (~ (v1_partfun1 @ X21 @ X20)
% 0.49/0.68          | ((k1_relat_1 @ X21) = (X20))
% 0.49/0.68          | ~ (v4_relat_1 @ X21 @ X20)
% 0.49/0.68          | ~ (v1_relat_1 @ X21))),
% 0.49/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.68        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.49/0.68        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.49/0.68  thf('39', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(cc2_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.49/0.68          | (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ 
% 0.49/0.68           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.49/0.68        | (v1_relat_1 @ sk_C))),
% 0.49/0.68      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.68  thf(fc6_relat_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.68  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.68  thf('44', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(cc2_relset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         ((v4_relat_1 @ X11 @ X12)
% 0.49/0.68          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.68  thf('46', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.68  thf('47', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.49/0.68  thf('48', plain,
% 0.49/0.68      (![X29 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf('49', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('clc', [status(thm)], ['28', '35'])).
% 0.49/0.68  thf('50', plain,
% 0.49/0.68      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup+', [status(thm)], ['48', '49'])).
% 0.49/0.68  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('52', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['50', '51'])).
% 0.49/0.68  thf('53', plain,
% 0.49/0.68      (![X20 : $i, X21 : $i]:
% 0.49/0.68         (~ (v1_partfun1 @ X21 @ X20)
% 0.49/0.68          | ((k1_relat_1 @ X21) = (X20))
% 0.49/0.68          | ~ (v4_relat_1 @ X21 @ X20)
% 0.49/0.68          | ~ (v1_relat_1 @ X21))),
% 0.49/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.68  thf('54', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.68        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.49/0.68        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['52', '53'])).
% 0.49/0.68  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.68  thf('56', plain,
% 0.49/0.68      (![X29 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf('57', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('58', plain,
% 0.49/0.68      (((m1_subset_1 @ sk_C @ 
% 0.49/0.68         (k1_zfmisc_1 @ 
% 0.49/0.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup+', [status(thm)], ['56', '57'])).
% 0.49/0.68  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('60', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_C @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.68      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.68  thf('61', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         ((v4_relat_1 @ X11 @ X12)
% 0.49/0.68          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.68  thf('62', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.49/0.68  thf('63', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['54', '55', '62'])).
% 0.49/0.68  thf('64', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['47', '63'])).
% 0.49/0.68  thf('65', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['47', '63'])).
% 0.49/0.68  thf('66', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['47', '63'])).
% 0.49/0.68  thf('67', plain,
% 0.49/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ 
% 0.49/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.68           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.68          sk_C)),
% 0.49/0.68      inference('demod', [status(thm)], ['10', '64', '65', '66'])).
% 0.49/0.68  thf('68', plain,
% 0.49/0.68      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ 
% 0.49/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.68            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.68           sk_C)
% 0.49/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['0', '67'])).
% 0.49/0.68  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.68  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('71', plain,
% 0.49/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ 
% 0.49/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.68           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.49/0.68          sk_C)),
% 0.49/0.68      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.49/0.68  thf('72', plain,
% 0.49/0.69      (![X29 : $i]:
% 0.49/0.69         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.69  thf('73', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.69      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.69  thf('74', plain,
% 0.49/0.69      (((m1_subset_1 @ sk_C @ 
% 0.49/0.69         (k1_zfmisc_1 @ 
% 0.49/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.49/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.69      inference('sup+', [status(thm)], ['72', '73'])).
% 0.49/0.69  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('76', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.49/0.69      inference('demod', [status(thm)], ['74', '75'])).
% 0.49/0.69  thf('77', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.69  thf('78', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.69      inference('demod', [status(thm)], ['76', '77'])).
% 0.49/0.69  thf(d4_tops_2, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.69       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.49/0.69         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.49/0.69  thf('79', plain,
% 0.49/0.69      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.49/0.69         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.49/0.69          | ~ (v2_funct_1 @ X33)
% 0.49/0.69          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.49/0.69          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.49/0.69          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.49/0.69          | ~ (v1_funct_1 @ X33))),
% 0.49/0.69      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.49/0.69  thf('80', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.49/0.69        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.69            = (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.69        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.69            != (k2_relat_1 @ sk_C)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.69  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('82', plain,
% 0.49/0.69      (![X29 : $i]:
% 0.49/0.69         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.69  thf('83', plain,
% 0.49/0.69      (![X29 : $i]:
% 0.49/0.69         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.69  thf('84', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('85', plain,
% 0.49/0.69      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.69      inference('sup+', [status(thm)], ['83', '84'])).
% 0.49/0.69  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('87', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['85', '86'])).
% 0.49/0.69  thf('88', plain,
% 0.49/0.69      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.49/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.69      inference('sup+', [status(thm)], ['82', '87'])).
% 0.49/0.69  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('90', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['88', '89'])).
% 0.49/0.69  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.69  thf('92', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['90', '91'])).
% 0.49/0.69  thf('93', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('94', plain,
% 0.49/0.69      (![X29 : $i]:
% 0.49/0.69         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.69  thf('95', plain,
% 0.49/0.69      (![X29 : $i]:
% 0.49/0.69         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.69  thf('96', plain,
% 0.49/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.69         = (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('97', plain,
% 0.49/0.69      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.69          = (k2_struct_0 @ sk_B))
% 0.49/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.69      inference('sup+', [status(thm)], ['95', '96'])).
% 0.49/0.69  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('99', plain,
% 0.49/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.69         = (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['97', '98'])).
% 0.49/0.69  thf('100', plain,
% 0.49/0.69      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.69          = (k2_struct_0 @ sk_B))
% 0.49/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.69      inference('sup+', [status(thm)], ['94', '99'])).
% 0.49/0.69  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('102', plain,
% 0.49/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.69         = (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['100', '101'])).
% 0.49/0.69  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.69  thf('104', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.69  thf('105', plain,
% 0.49/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.69         = (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.49/0.69  thf('106', plain,
% 0.49/0.69      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.69          = (k2_funct_1 @ sk_C))
% 0.49/0.69        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.49/0.69      inference('demod', [status(thm)], ['80', '81', '92', '93', '105'])).
% 0.49/0.69  thf('107', plain,
% 0.49/0.69      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.69         = (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['106'])).
% 0.49/0.69  thf('108', plain,
% 0.49/0.69      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ 
% 0.49/0.69          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69           (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69          sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['71', '107'])).
% 0.49/0.69  thf('109', plain,
% 0.49/0.69      (![X29 : $i]:
% 0.49/0.69         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.69  thf('110', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.69      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.69  thf(t31_funct_2, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.69       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.49/0.69         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.49/0.69           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.49/0.69           ( m1_subset_1 @
% 0.49/0.69             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.49/0.69  thf('111', plain,
% 0.49/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X26)
% 0.49/0.69          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.49/0.69          | (m1_subset_1 @ (k2_funct_1 @ X26) @ 
% 0.49/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.49/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.49/0.69          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.49/0.69          | ~ (v1_funct_1 @ X26))),
% 0.49/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.69  thf('112', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69           (k1_zfmisc_1 @ 
% 0.49/0.69            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.49/0.69        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.69            != (u1_struct_0 @ sk_B))
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['110', '111'])).
% 0.49/0.69  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('114', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['85', '86'])).
% 0.49/0.69  thf('115', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.69      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.69  thf('116', plain,
% 0.49/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.69         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.49/0.69          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.49/0.69  thf('117', plain,
% 0.49/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.69         = (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['115', '116'])).
% 0.49/0.69  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('119', plain,
% 0.49/0.69      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69         (k1_zfmisc_1 @ 
% 0.49/0.69          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.49/0.69        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.49/0.69      inference('demod', [status(thm)], ['112', '113', '114', '117', '118'])).
% 0.49/0.69  thf('120', plain,
% 0.49/0.69      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.49/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.49/0.69        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69           (k1_zfmisc_1 @ 
% 0.49/0.69            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['109', '119'])).
% 0.49/0.69  thf('121', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.69  thf('122', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('123', plain,
% 0.49/0.69      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.49/0.69        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69           (k1_zfmisc_1 @ 
% 0.49/0.69            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.49/0.69      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.49/0.69  thf('124', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.49/0.69      inference('simplify', [status(thm)], ['123'])).
% 0.49/0.69  thf('125', plain,
% 0.49/0.69      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.49/0.69         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.49/0.69          | ~ (v2_funct_1 @ X33)
% 0.49/0.69          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.49/0.69          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.49/0.69          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.49/0.69          | ~ (v1_funct_1 @ X33))),
% 0.49/0.69      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.49/0.69  thf('126', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69             (k2_struct_0 @ sk_A))
% 0.49/0.69        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['124', '125'])).
% 0.49/0.69  thf('127', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.69      inference('demod', [status(thm)], ['76', '77'])).
% 0.49/0.69  thf('128', plain,
% 0.49/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X26)
% 0.49/0.69          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.49/0.69          | (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.49/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.49/0.69          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.49/0.69          | ~ (v1_funct_1 @ X26))),
% 0.49/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.69  thf('129', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.49/0.69        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.69            != (k2_relat_1 @ sk_C))
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['127', '128'])).
% 0.49/0.69  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('131', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['90', '91'])).
% 0.49/0.69  thf('132', plain,
% 0.49/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.69         = (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.49/0.69  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('134', plain,
% 0.49/0.69      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.49/0.69      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 0.49/0.69  thf('135', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['134'])).
% 0.49/0.69  thf('136', plain,
% 0.49/0.69      (![X29 : $i]:
% 0.49/0.69         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.69  thf('137', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.69      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.69  thf('138', plain,
% 0.49/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X26)
% 0.49/0.69          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.49/0.69          | (v1_funct_2 @ (k2_funct_1 @ X26) @ X27 @ X28)
% 0.49/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.49/0.69          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.49/0.69          | ~ (v1_funct_1 @ X26))),
% 0.49/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.69  thf('139', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69           (k2_struct_0 @ sk_A))
% 0.49/0.69        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.69            != (u1_struct_0 @ sk_B))
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['137', '138'])).
% 0.49/0.69  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('141', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['85', '86'])).
% 0.49/0.69  thf('142', plain,
% 0.49/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.69         = (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['115', '116'])).
% 0.49/0.69  thf('143', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('144', plain,
% 0.49/0.69      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69         (k2_struct_0 @ sk_A))
% 0.49/0.69        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.49/0.69      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 0.49/0.69  thf('145', plain,
% 0.49/0.69      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.49/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.49/0.69        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69           (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['136', '144'])).
% 0.49/0.69  thf('146', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.69      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.69  thf('147', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('148', plain,
% 0.49/0.69      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.49/0.69        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69           (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.49/0.69  thf('149', plain,
% 0.49/0.69      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69        (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('simplify', [status(thm)], ['148'])).
% 0.49/0.69  thf(t55_funct_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.69       ( ( v2_funct_1 @ A ) =>
% 0.49/0.69         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.49/0.69           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.49/0.69  thf('150', plain,
% 0.49/0.69      (![X8 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X8)
% 0.49/0.69          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.49/0.69          | ~ (v1_funct_1 @ X8)
% 0.49/0.69          | ~ (v1_relat_1 @ X8))),
% 0.49/0.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.49/0.69  thf('151', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.69      inference('demod', [status(thm)], ['76', '77'])).
% 0.49/0.69  thf('152', plain,
% 0.49/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X26)
% 0.49/0.69          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.49/0.69          | (m1_subset_1 @ (k2_funct_1 @ X26) @ 
% 0.49/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.49/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.49/0.69          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.49/0.69          | ~ (v1_funct_1 @ X26))),
% 0.49/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.69  thf('153', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.49/0.69        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69           (k1_zfmisc_1 @ 
% 0.49/0.69            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.49/0.69        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.69            != (k2_relat_1 @ sk_C))
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['151', '152'])).
% 0.49/0.69  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('155', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['90', '91'])).
% 0.49/0.69  thf('156', plain,
% 0.49/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.69         = (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.49/0.69  thf('157', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('158', plain,
% 0.49/0.69      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69         (k1_zfmisc_1 @ 
% 0.49/0.69          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.49/0.69        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.49/0.69      inference('demod', [status(thm)], ['153', '154', '155', '156', '157'])).
% 0.49/0.69  thf('159', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.49/0.69      inference('simplify', [status(thm)], ['158'])).
% 0.49/0.69  thf('160', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.49/0.69          | (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.49/0.69  thf('161', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ 
% 0.49/0.69           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A)))
% 0.49/0.69        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['159', '160'])).
% 0.49/0.69  thf('162', plain,
% 0.49/0.69      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.49/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.69  thf('163', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['161', '162'])).
% 0.49/0.69  thf(t61_funct_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.69       ( ( v2_funct_1 @ A ) =>
% 0.49/0.69         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.49/0.69             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.49/0.69           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.49/0.69             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.69  thf('164', plain,
% 0.49/0.69      (![X9 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X9)
% 0.49/0.69          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 0.49/0.69              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.49/0.69          | ~ (v1_funct_1 @ X9)
% 0.49/0.69          | ~ (v1_relat_1 @ X9))),
% 0.49/0.69      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.49/0.69  thf(t48_funct_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.69           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.49/0.69               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.49/0.69             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.49/0.69  thf('165', plain,
% 0.49/0.69      (![X6 : $i, X7 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ X6)
% 0.49/0.69          | ~ (v1_funct_1 @ X6)
% 0.49/0.69          | (v2_funct_1 @ X6)
% 0.49/0.69          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.49/0.69          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 0.49/0.69          | ~ (v1_funct_1 @ X7)
% 0.49/0.69          | ~ (v1_relat_1 @ X7))),
% 0.49/0.69      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.49/0.69  thf('166', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.49/0.69          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['164', '165'])).
% 0.49/0.69  thf(fc4_funct_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.49/0.69       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.49/0.69  thf('167', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.49/0.69      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.49/0.69  thf('168', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.49/0.69          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.69      inference('demod', [status(thm)], ['166', '167'])).
% 0.49/0.69  thf('169', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ X0))),
% 0.49/0.69      inference('simplify', [status(thm)], ['168'])).
% 0.49/0.69  thf('170', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.69        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.49/0.69        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['163', '169'])).
% 0.49/0.69  thf('171', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('174', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['54', '55', '62'])).
% 0.49/0.69  thf('175', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['134'])).
% 0.49/0.69  thf('176', plain,
% 0.49/0.69      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.49/0.69        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('demod', [status(thm)],
% 0.49/0.69                ['170', '171', '172', '173', '174', '175'])).
% 0.49/0.69  thf('177', plain,
% 0.49/0.69      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.49/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.69        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['150', '176'])).
% 0.49/0.69  thf('178', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['54', '55', '62'])).
% 0.49/0.69  thf('179', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('181', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('182', plain,
% 0.49/0.69      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.49/0.69        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('demod', [status(thm)], ['177', '178', '179', '180', '181'])).
% 0.49/0.69  thf('183', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['182'])).
% 0.49/0.69  thf('184', plain,
% 0.49/0.69      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['126', '135', '149', '183'])).
% 0.49/0.69  thf(t65_funct_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.69       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.49/0.69  thf('185', plain,
% 0.49/0.69      (![X10 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X10)
% 0.49/0.69          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.49/0.69          | ~ (v1_funct_1 @ X10)
% 0.49/0.69          | ~ (v1_relat_1 @ X10))),
% 0.49/0.69      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.69  thf('186', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.49/0.69      inference('simplify', [status(thm)], ['123'])).
% 0.49/0.69  thf('187', plain,
% 0.49/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X26)
% 0.49/0.69          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.49/0.69          | (m1_subset_1 @ (k2_funct_1 @ X26) @ 
% 0.49/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.49/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.49/0.69          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.49/0.69          | ~ (v1_funct_1 @ X26))),
% 0.49/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.69  thf('188', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69             (k2_struct_0 @ sk_A))
% 0.49/0.69        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69           (k1_zfmisc_1 @ 
% 0.49/0.69            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.49/0.69        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['186', '187'])).
% 0.49/0.69  thf('189', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['134'])).
% 0.49/0.69  thf('190', plain,
% 0.49/0.69      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69        (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('simplify', [status(thm)], ['148'])).
% 0.49/0.69  thf('191', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['182'])).
% 0.49/0.69  thf('192', plain,
% 0.49/0.69      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69         (k1_zfmisc_1 @ 
% 0.49/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 0.49/0.69  thf('193', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.49/0.69      inference('simplify', [status(thm)], ['123'])).
% 0.49/0.69  thf('194', plain,
% 0.49/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.69         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.49/0.69          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.49/0.69  thf('195', plain,
% 0.49/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['193', '194'])).
% 0.49/0.69  thf('196', plain,
% 0.49/0.69      (![X8 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X8)
% 0.49/0.69          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.49/0.69          | ~ (v1_funct_1 @ X8)
% 0.49/0.69          | ~ (v1_relat_1 @ X8))),
% 0.49/0.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.49/0.69  thf('197', plain,
% 0.49/0.69      (![X8 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X8)
% 0.49/0.69          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.49/0.69          | ~ (v1_funct_1 @ X8)
% 0.49/0.69          | ~ (v1_relat_1 @ X8))),
% 0.49/0.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.49/0.69  thf('198', plain,
% 0.49/0.69      (![X10 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X10)
% 0.49/0.69          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.49/0.69          | ~ (v1_funct_1 @ X10)
% 0.49/0.69          | ~ (v1_relat_1 @ X10))),
% 0.49/0.69      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.69  thf('199', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['182'])).
% 0.49/0.69  thf('200', plain,
% 0.49/0.69      (![X10 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X10)
% 0.49/0.69          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.49/0.69          | ~ (v1_funct_1 @ X10)
% 0.49/0.69          | ~ (v1_relat_1 @ X10))),
% 0.49/0.69      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.69  thf('201', plain,
% 0.49/0.69      (![X8 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X8)
% 0.49/0.69          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.49/0.69          | ~ (v1_funct_1 @ X8)
% 0.49/0.69          | ~ (v1_relat_1 @ X8))),
% 0.49/0.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.49/0.69  thf('202', plain,
% 0.49/0.69      (![X10 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X10)
% 0.49/0.69          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.49/0.69          | ~ (v1_funct_1 @ X10)
% 0.49/0.69          | ~ (v1_relat_1 @ X10))),
% 0.49/0.69      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.69  thf('203', plain,
% 0.49/0.69      (![X8 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X8)
% 0.49/0.69          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.49/0.69          | ~ (v1_funct_1 @ X8)
% 0.49/0.69          | ~ (v1_relat_1 @ X8))),
% 0.49/0.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.49/0.69  thf('204', plain,
% 0.49/0.69      (![X20 : $i, X21 : $i]:
% 0.49/0.69         (((k1_relat_1 @ X21) != (X20))
% 0.49/0.69          | (v1_partfun1 @ X21 @ X20)
% 0.49/0.69          | ~ (v4_relat_1 @ X21 @ X20)
% 0.49/0.69          | ~ (v1_relat_1 @ X21))),
% 0.49/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.69  thf('205', plain,
% 0.49/0.69      (![X21 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ X21)
% 0.49/0.69          | ~ (v4_relat_1 @ X21 @ (k1_relat_1 @ X21))
% 0.49/0.69          | (v1_partfun1 @ X21 @ (k1_relat_1 @ X21)))),
% 0.49/0.69      inference('simplify', [status(thm)], ['204'])).
% 0.49/0.69  thf('206', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['203', '205'])).
% 0.49/0.69  thf('207', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.69          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.49/0.69             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['202', '206'])).
% 0.49/0.69  thf('208', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.49/0.69             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['201', '207'])).
% 0.49/0.69  thf('209', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.49/0.69          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.49/0.69             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.49/0.69      inference('simplify', [status(thm)], ['208'])).
% 0.49/0.69  thf('210', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.49/0.69             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['200', '209'])).
% 0.49/0.69  thf('211', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.49/0.69           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.49/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.49/0.69          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.49/0.69          | ~ (v2_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_relat_1 @ X0))),
% 0.49/0.69      inference('simplify', [status(thm)], ['210'])).
% 0.49/0.69  thf('212', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.49/0.69        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['199', '211'])).
% 0.49/0.69  thf('213', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('214', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('215', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('216', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['54', '55', '62'])).
% 0.49/0.69  thf('217', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['60', '61'])).
% 0.49/0.69  thf('218', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['161', '162'])).
% 0.49/0.69  thf('219', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['134'])).
% 0.49/0.69  thf('220', plain,
% 0.49/0.69      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.69      inference('demod', [status(thm)],
% 0.49/0.69                ['212', '213', '214', '215', '216', '217', '218', '219'])).
% 0.49/0.69  thf('221', plain,
% 0.49/0.69      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.49/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.69      inference('sup+', [status(thm)], ['198', '220'])).
% 0.49/0.69  thf('222', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('223', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('224', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('225', plain,
% 0.49/0.69      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.69      inference('demod', [status(thm)], ['221', '222', '223', '224'])).
% 0.49/0.69  thf('226', plain,
% 0.49/0.69      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['197', '225'])).
% 0.49/0.69  thf('227', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['161', '162'])).
% 0.49/0.69  thf('228', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['134'])).
% 0.49/0.69  thf('229', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['182'])).
% 0.49/0.69  thf('230', plain,
% 0.49/0.69      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('demod', [status(thm)], ['226', '227', '228', '229'])).
% 0.49/0.69  thf('231', plain,
% 0.49/0.69      (![X20 : $i, X21 : $i]:
% 0.49/0.69         (~ (v1_partfun1 @ X21 @ X20)
% 0.49/0.69          | ((k1_relat_1 @ X21) = (X20))
% 0.49/0.69          | ~ (v4_relat_1 @ X21 @ X20)
% 0.49/0.69          | ~ (v1_relat_1 @ X21))),
% 0.49/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.69  thf('232', plain,
% 0.49/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['230', '231'])).
% 0.49/0.69  thf('233', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('234', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['54', '55', '62'])).
% 0.49/0.69  thf('235', plain,
% 0.49/0.69      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.69      inference('demod', [status(thm)], ['232', '233', '234'])).
% 0.49/0.69  thf('236', plain,
% 0.49/0.69      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.49/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.69        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['196', '235'])).
% 0.49/0.69  thf('237', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['54', '55', '62'])).
% 0.49/0.69  thf('238', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['60', '61'])).
% 0.49/0.69  thf('239', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('240', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('241', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('242', plain,
% 0.49/0.69      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('demod', [status(thm)],
% 0.49/0.69                ['236', '237', '238', '239', '240', '241'])).
% 0.49/0.69  thf('243', plain,
% 0.49/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['195', '242'])).
% 0.49/0.69  thf('244', plain,
% 0.49/0.69      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69         (k1_zfmisc_1 @ 
% 0.49/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.69        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['192', '243'])).
% 0.49/0.69  thf('245', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.69      inference('simplify', [status(thm)], ['244'])).
% 0.49/0.69  thf('246', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.69      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.69  thf(redefinition_r2_funct_2, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.69         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.49/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.69       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.49/0.69  thf('247', plain,
% 0.49/0.69      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.49/0.69          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.49/0.69          | ~ (v1_funct_1 @ X22)
% 0.49/0.69          | ~ (v1_funct_1 @ X25)
% 0.49/0.69          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.49/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.49/0.69          | ((X22) = (X25))
% 0.49/0.69          | ~ (r2_funct_2 @ X23 @ X24 @ X22 @ X25))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.49/0.69  thf('248', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.69             X0)
% 0.49/0.69          | ((sk_C) = (X0))
% 0.49/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.49/0.69               (k1_zfmisc_1 @ 
% 0.49/0.69                (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.69          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69          | ~ (v1_funct_1 @ X0)
% 0.49/0.69          | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['246', '247'])).
% 0.49/0.69  thf('249', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('250', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['85', '86'])).
% 0.49/0.69  thf('251', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.69             X0)
% 0.49/0.69          | ((sk_C) = (X0))
% 0.49/0.69          | ~ (m1_subset_1 @ X0 @ 
% 0.49/0.69               (k1_zfmisc_1 @ 
% 0.49/0.69                (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.69          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69          | ~ (v1_funct_1 @ X0))),
% 0.49/0.69      inference('demod', [status(thm)], ['248', '249', '250'])).
% 0.49/0.69  thf('252', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69             (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.69             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['245', '251'])).
% 0.49/0.69  thf('253', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.49/0.69      inference('simplify', [status(thm)], ['123'])).
% 0.49/0.69  thf('254', plain,
% 0.49/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X26)
% 0.49/0.69          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.49/0.69          | (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.49/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.49/0.69          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.49/0.69          | ~ (v1_funct_1 @ X26))),
% 0.49/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.69  thf('255', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69             (k2_struct_0 @ sk_A))
% 0.49/0.69        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.49/0.69        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['253', '254'])).
% 0.49/0.69  thf('256', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['134'])).
% 0.49/0.69  thf('257', plain,
% 0.49/0.69      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69        (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('simplify', [status(thm)], ['148'])).
% 0.49/0.69  thf('258', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['182'])).
% 0.49/0.69  thf('259', plain,
% 0.49/0.69      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['255', '256', '257', '258'])).
% 0.49/0.69  thf('260', plain,
% 0.49/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['195', '242'])).
% 0.49/0.69  thf('261', plain,
% 0.49/0.69      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['259', '260'])).
% 0.49/0.69  thf('262', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('simplify', [status(thm)], ['261'])).
% 0.49/0.69  thf('263', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.49/0.69      inference('simplify', [status(thm)], ['123'])).
% 0.49/0.69  thf('264', plain,
% 0.49/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (v2_funct_1 @ X26)
% 0.49/0.69          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.49/0.69          | (v1_funct_2 @ (k2_funct_1 @ X26) @ X27 @ X28)
% 0.49/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.49/0.69          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.49/0.69          | ~ (v1_funct_1 @ X26))),
% 0.49/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.69  thf('265', plain,
% 0.49/0.69      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.69        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69             (k2_struct_0 @ sk_A))
% 0.49/0.69        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69           (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.49/0.69        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['263', '264'])).
% 0.49/0.69  thf('266', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['134'])).
% 0.49/0.69  thf('267', plain,
% 0.49/0.69      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.69        (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('simplify', [status(thm)], ['148'])).
% 0.49/0.69  thf('268', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['182'])).
% 0.49/0.69  thf('269', plain,
% 0.49/0.69      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69         (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['265', '266', '267', '268'])).
% 0.49/0.69  thf('270', plain,
% 0.49/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['195', '242'])).
% 0.49/0.69  thf('271', plain,
% 0.49/0.69      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69         (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['269', '270'])).
% 0.49/0.69  thf('272', plain,
% 0.49/0.69      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.49/0.69        (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.69      inference('simplify', [status(thm)], ['271'])).
% 0.49/0.69  thf('273', plain,
% 0.49/0.69      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.69        | ~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.69             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.69      inference('demod', [status(thm)], ['252', '262', '272'])).
% 0.49/0.69  thf('274', plain,
% 0.49/0.69      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.69           sk_C)
% 0.49/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.69        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['185', '273'])).
% 0.49/0.69  thf('275', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.69      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.69  thf('276', plain,
% 0.49/0.69      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.49/0.69          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.49/0.69          | ~ (v1_funct_1 @ X22)
% 0.49/0.69          | ~ (v1_funct_1 @ X25)
% 0.49/0.69          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.49/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.49/0.69          | (r2_funct_2 @ X23 @ X24 @ X22 @ X25)
% 0.49/0.69          | ((X22) != (X25)))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.49/0.69  thf('277', plain,
% 0.49/0.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.49/0.69         ((r2_funct_2 @ X23 @ X24 @ X25 @ X25)
% 0.49/0.69          | ~ (v1_funct_1 @ X25)
% 0.49/0.69          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.49/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.49/0.69      inference('simplify', [status(thm)], ['276'])).
% 0.49/0.69  thf('278', plain,
% 0.49/0.69      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.49/0.69           sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['275', '277'])).
% 0.49/0.69  thf('279', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.69      inference('demod', [status(thm)], ['85', '86'])).
% 0.49/0.69  thf('280', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('281', plain,
% 0.49/0.69      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['278', '279', '280'])).
% 0.49/0.69  thf('282', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('283', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('284', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('285', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.69      inference('demod', [status(thm)], ['274', '281', '282', '283', '284'])).
% 0.49/0.69  thf('286', plain,
% 0.49/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['195', '242'])).
% 0.49/0.69  thf('287', plain,
% 0.49/0.69      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.49/0.69        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['184', '285', '286'])).
% 0.49/0.69  thf('288', plain,
% 0.49/0.69      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.69         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.49/0.69      inference('simplify', [status(thm)], ['287'])).
% 0.49/0.69  thf('289', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C @ 
% 0.49/0.69        (k1_zfmisc_1 @ 
% 0.49/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.69      inference('demod', [status(thm)], ['76', '77'])).
% 0.49/0.69  thf('290', plain,
% 0.49/0.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.49/0.69         ((r2_funct_2 @ X23 @ X24 @ X25 @ X25)
% 0.49/0.69          | ~ (v1_funct_1 @ X25)
% 0.49/0.69          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.49/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.49/0.69      inference('simplify', [status(thm)], ['276'])).
% 0.49/0.69  thf('291', plain,
% 0.49/0.69      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.49/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.69        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ 
% 0.49/0.69           sk_C))),
% 0.49/0.69      inference('sup-', [status(thm)], ['289', '290'])).
% 0.49/0.69  thf('292', plain,
% 0.49/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.49/0.69      inference('demod', [status(thm)], ['90', '91'])).
% 0.49/0.69  thf('293', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('294', plain,
% 0.49/0.69      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ sk_C)),
% 0.49/0.69      inference('demod', [status(thm)], ['291', '292', '293'])).
% 0.49/0.69  thf('295', plain, ($false),
% 0.49/0.69      inference('demod', [status(thm)], ['108', '288', '294'])).
% 0.49/0.69  
% 0.49/0.69  % SZS output end Refutation
% 0.49/0.69  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
