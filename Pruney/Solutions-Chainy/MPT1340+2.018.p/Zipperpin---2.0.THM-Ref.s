%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CJEHfas1Tt

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:08 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  274 (2243 expanded)
%              Number of leaves         :   47 ( 680 expanded)
%              Depth                    :   32
%              Number of atoms          : 2620 (49938 expanded)
%              Number of equality atoms :  151 (1578 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ( ( k5_relat_1 @ X30 @ ( k2_funct_1 @ X30 ) )
        = ( k6_partfun1 @ X31 ) )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X31 @ X29 @ X30 )
       != X29 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ( ( k5_relat_1 @ X30 @ ( k2_funct_1 @ X30 ) )
        = ( k6_relat_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X31 @ X29 @ X30 )
       != X29 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','24','25','34','35'])).

thf('37',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

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

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('39',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('46',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('53',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('57',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('63',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40','51','60','65','66','69'])).

thf('71',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X26 ) @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('93',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','90','93'])).

thf('95',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['77','94'])).

thf('96',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('97',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('98',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('99',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('101',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('102',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('103',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('104',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != X16 )
      | ( v1_partfun1 @ X17 @ X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('105',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v4_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
      | ( v1_partfun1 @ X17 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
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
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,(
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
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
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
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['99','111'])).

thf('113',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('114',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('115',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('117',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('118',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('124',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('127',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('128',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','128'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('130',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('131',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('132',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('133',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['115','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('141',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('142',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','139','142','143','144','145'])).

thf('147',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf('152',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','151'])).

thf('153',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('154',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('155',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('157',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('159',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('162',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','162'])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('165',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['163','164','165','166','167','168'])).

thf('170',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['95','169'])).

thf('171',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('173',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['171','176'])).

thf('178',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('182',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('184',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('185',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['179','182','183','184'])).

thf('186',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('187',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('188',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('193',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['188','189','190','191','192'])).

thf('194',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['185','194'])).

thf('196',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['170','195'])).

thf('197',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('199',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('200',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_funct_2 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('206',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('207',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['198','208'])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('212',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('214',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['197','212','213','214','215'])).

thf('217',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('218',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['216','220'])).

thf('222',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('223',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,(
    $false ),
    inference(demod,[status(thm)],['0','224'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CJEHfas1Tt
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.85  % Solved by: fo/fo7.sh
% 0.67/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.85  % done 658 iterations in 0.395s
% 0.67/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.85  % SZS output start Refutation
% 0.67/0.85  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.67/0.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.67/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.85  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.67/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.85  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.67/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.85  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.67/0.85  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.67/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.67/0.85  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.67/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.85  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.67/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.85  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.67/0.85  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.67/0.85  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.67/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.67/0.85  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.67/0.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.85  thf(t64_tops_2, conjecture,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( l1_struct_0 @ A ) =>
% 0.67/0.85       ( ![B:$i]:
% 0.67/0.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.67/0.85           ( ![C:$i]:
% 0.67/0.85             ( ( ( v1_funct_1 @ C ) & 
% 0.67/0.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.67/0.85                 ( m1_subset_1 @
% 0.67/0.85                   C @ 
% 0.67/0.85                   ( k1_zfmisc_1 @
% 0.67/0.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.67/0.85               ( ( ( ( k2_relset_1 @
% 0.67/0.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.67/0.85                     ( k2_struct_0 @ B ) ) & 
% 0.67/0.85                   ( v2_funct_1 @ C ) ) =>
% 0.67/0.85                 ( r2_funct_2 @
% 0.67/0.85                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.67/0.85                   ( k2_tops_2 @
% 0.67/0.85                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.67/0.85                     ( k2_tops_2 @
% 0.67/0.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.67/0.85                   C ) ) ) ) ) ) ))).
% 0.67/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.85    (~( ![A:$i]:
% 0.67/0.85        ( ( l1_struct_0 @ A ) =>
% 0.67/0.85          ( ![B:$i]:
% 0.67/0.85            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.67/0.85              ( ![C:$i]:
% 0.67/0.85                ( ( ( v1_funct_1 @ C ) & 
% 0.67/0.85                    ( v1_funct_2 @
% 0.67/0.85                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.67/0.85                    ( m1_subset_1 @
% 0.67/0.85                      C @ 
% 0.67/0.85                      ( k1_zfmisc_1 @
% 0.67/0.85                        ( k2_zfmisc_1 @
% 0.67/0.85                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.67/0.85                  ( ( ( ( k2_relset_1 @
% 0.67/0.85                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.67/0.85                        ( k2_struct_0 @ B ) ) & 
% 0.67/0.85                      ( v2_funct_1 @ C ) ) =>
% 0.67/0.85                    ( r2_funct_2 @
% 0.67/0.85                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.67/0.85                      ( k2_tops_2 @
% 0.67/0.85                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.67/0.85                        ( k2_tops_2 @
% 0.67/0.85                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.67/0.85                      C ) ) ) ) ) ) ) )),
% 0.67/0.85    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.67/0.85  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf(t65_funct_1, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.85       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.67/0.85  thf('1', plain,
% 0.67/0.85      (![X6 : $i]:
% 0.67/0.85         (~ (v2_funct_1 @ X6)
% 0.67/0.85          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.67/0.85          | ~ (v1_funct_1 @ X6)
% 0.67/0.85          | ~ (v1_relat_1 @ X6))),
% 0.67/0.85      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.67/0.85  thf(t55_funct_1, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.85       ( ( v2_funct_1 @ A ) =>
% 0.67/0.85         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.67/0.85           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.67/0.85  thf('2', plain,
% 0.67/0.85      (![X5 : $i]:
% 0.67/0.85         (~ (v2_funct_1 @ X5)
% 0.67/0.85          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.67/0.85          | ~ (v1_funct_1 @ X5)
% 0.67/0.85          | ~ (v1_relat_1 @ X5))),
% 0.67/0.85      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.85  thf(d3_struct_0, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.67/0.85  thf('3', plain,
% 0.67/0.85      (![X32 : $i]:
% 0.67/0.85         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.85  thf('4', plain,
% 0.67/0.85      (![X32 : $i]:
% 0.67/0.85         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.85  thf('5', plain,
% 0.67/0.85      ((m1_subset_1 @ sk_C @ 
% 0.67/0.85        (k1_zfmisc_1 @ 
% 0.67/0.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('6', plain,
% 0.67/0.85      (((m1_subset_1 @ sk_C @ 
% 0.67/0.85         (k1_zfmisc_1 @ 
% 0.67/0.85          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.67/0.85        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.85      inference('sup+', [status(thm)], ['4', '5'])).
% 0.67/0.85  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('8', plain,
% 0.67/0.85      ((m1_subset_1 @ sk_C @ 
% 0.67/0.85        (k1_zfmisc_1 @ 
% 0.67/0.85         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.85      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.85  thf('9', plain,
% 0.67/0.85      (((m1_subset_1 @ sk_C @ 
% 0.67/0.85         (k1_zfmisc_1 @ 
% 0.67/0.85          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.67/0.85        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.85      inference('sup+', [status(thm)], ['3', '8'])).
% 0.67/0.85  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('11', plain,
% 0.67/0.85      ((m1_subset_1 @ sk_C @ 
% 0.67/0.85        (k1_zfmisc_1 @ 
% 0.67/0.85         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.85      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.85  thf(t35_funct_2, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i]:
% 0.67/0.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.85       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.67/0.85         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.67/0.85           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.67/0.85             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.67/0.85  thf('12', plain,
% 0.67/0.85      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.67/0.85         (((X29) = (k1_xboole_0))
% 0.67/0.85          | ~ (v1_funct_1 @ X30)
% 0.67/0.85          | ~ (v1_funct_2 @ X30 @ X31 @ X29)
% 0.67/0.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.67/0.85          | ((k5_relat_1 @ X30 @ (k2_funct_1 @ X30)) = (k6_partfun1 @ X31))
% 0.67/0.85          | ~ (v2_funct_1 @ X30)
% 0.67/0.85          | ((k2_relset_1 @ X31 @ X29 @ X30) != (X29)))),
% 0.67/0.85      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.67/0.85  thf(redefinition_k6_partfun1, axiom,
% 0.67/0.85    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.67/0.85  thf('13', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.67/0.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.85  thf('14', plain,
% 0.67/0.85      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.67/0.85         (((X29) = (k1_xboole_0))
% 0.67/0.85          | ~ (v1_funct_1 @ X30)
% 0.67/0.85          | ~ (v1_funct_2 @ X30 @ X31 @ X29)
% 0.67/0.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.67/0.85          | ((k5_relat_1 @ X30 @ (k2_funct_1 @ X30)) = (k6_relat_1 @ X31))
% 0.67/0.85          | ~ (v2_funct_1 @ X30)
% 0.67/0.85          | ((k2_relset_1 @ X31 @ X29 @ X30) != (X29)))),
% 0.67/0.85      inference('demod', [status(thm)], ['12', '13'])).
% 0.67/0.85  thf('15', plain,
% 0.67/0.85      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.85          != (k2_struct_0 @ sk_B))
% 0.67/0.85        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.85        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.67/0.85            = (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.67/0.85        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.85        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.85        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.85      inference('sup-', [status(thm)], ['11', '14'])).
% 0.67/0.85  thf('16', plain,
% 0.67/0.85      (![X32 : $i]:
% 0.67/0.85         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.85  thf('17', plain,
% 0.67/0.85      (![X32 : $i]:
% 0.67/0.85         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.85  thf('18', plain,
% 0.67/0.85      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.85         = (k2_struct_0 @ sk_B))),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('19', plain,
% 0.67/0.85      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.85          = (k2_struct_0 @ sk_B))
% 0.67/0.85        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.85      inference('sup+', [status(thm)], ['17', '18'])).
% 0.67/0.85  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('21', plain,
% 0.67/0.85      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.85         = (k2_struct_0 @ sk_B))),
% 0.67/0.85      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.85  thf('22', plain,
% 0.67/0.85      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.85          = (k2_struct_0 @ sk_B))
% 0.67/0.85        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.85      inference('sup+', [status(thm)], ['16', '21'])).
% 0.67/0.85  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('24', plain,
% 0.67/0.85      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.85         = (k2_struct_0 @ sk_B))),
% 0.67/0.85      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.85  thf('25', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('26', plain,
% 0.67/0.85      (![X32 : $i]:
% 0.67/0.85         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('27', plain,
% 0.67/0.86      (![X32 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('28', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('29', plain,
% 0.67/0.86      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup+', [status(thm)], ['27', '28'])).
% 0.67/0.86  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('31', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['29', '30'])).
% 0.67/0.86  thf('32', plain,
% 0.67/0.86      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.86        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup+', [status(thm)], ['26', '31'])).
% 0.67/0.86  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('34', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.86  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('36', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.67/0.86        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.67/0.86            = (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('demod', [status(thm)], ['15', '24', '25', '34', '35'])).
% 0.67/0.86  thf('37', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.67/0.86            = (k6_relat_1 @ (k2_struct_0 @ sk_A))))),
% 0.67/0.86      inference('simplify', [status(thm)], ['36'])).
% 0.67/0.86  thf(t48_funct_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.67/0.86           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.67/0.86               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.67/0.86             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.67/0.86  thf('38', plain,
% 0.67/0.86      (![X3 : $i, X4 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ X3)
% 0.67/0.86          | ~ (v1_funct_1 @ X3)
% 0.67/0.86          | (v2_funct_1 @ X4)
% 0.67/0.86          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.67/0.86          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.67/0.86          | ~ (v1_funct_1 @ X4)
% 0.67/0.86          | ~ (v1_relat_1 @ X4))),
% 0.67/0.86      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.67/0.86  thf('39', plain,
% 0.67/0.86      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v1_relat_1 @ sk_C))),
% 0.67/0.86      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.86  thf(fc4_funct_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.67/0.86       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.67/0.86  thf('40', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.67/0.86      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.67/0.86  thf('41', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.86      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.86  thf(t31_funct_2, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.86       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.67/0.86         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.67/0.86           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.67/0.86           ( m1_subset_1 @
% 0.67/0.86             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.67/0.86  thf('42', plain,
% 0.67/0.86      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.86         (~ (v2_funct_1 @ X26)
% 0.67/0.86          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.67/0.86          | (m1_subset_1 @ (k2_funct_1 @ X26) @ 
% 0.67/0.86             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.67/0.86          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.67/0.86          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.67/0.86          | ~ (v1_funct_1 @ X26))),
% 0.67/0.86      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.67/0.86  thf('43', plain,
% 0.67/0.86      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.86        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.86           (k1_zfmisc_1 @ 
% 0.67/0.86            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.67/0.86        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86            != (k2_struct_0 @ sk_B))
% 0.67/0.86        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.86  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('45', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.86  thf('46', plain,
% 0.67/0.86      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86         = (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.86  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('48', plain,
% 0.67/0.86      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.86         (k1_zfmisc_1 @ 
% 0.67/0.86          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.67/0.86  thf('49', plain,
% 0.67/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.67/0.86      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.86  thf(cc1_relset_1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.86       ( v1_relat_1 @ C ) ))).
% 0.67/0.86  thf('50', plain,
% 0.67/0.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.67/0.86         ((v1_relat_1 @ X7)
% 0.67/0.86          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.86  thf('51', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.86      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.86  thf('52', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.86      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.86  thf('53', plain,
% 0.67/0.86      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.86         (~ (v2_funct_1 @ X26)
% 0.67/0.86          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.67/0.86          | (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.67/0.86          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.67/0.86          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.67/0.86          | ~ (v1_funct_1 @ X26))),
% 0.67/0.86      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.67/0.86  thf('54', plain,
% 0.67/0.86      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.86        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86            != (k2_struct_0 @ sk_B))
% 0.67/0.86        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.86      inference('sup-', [status(thm)], ['52', '53'])).
% 0.67/0.86  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('56', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.86  thf('57', plain,
% 0.67/0.86      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86         = (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.86  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('59', plain,
% 0.67/0.86      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.67/0.86  thf('60', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.86      inference('simplify', [status(thm)], ['59'])).
% 0.67/0.86  thf('61', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(redefinition_k2_relset_1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.86       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.67/0.86  thf('62', plain,
% 0.67/0.86      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.67/0.86         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.67/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.67/0.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.67/0.86  thf('63', plain,
% 0.67/0.86      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86         = (k2_relat_1 @ sk_C))),
% 0.67/0.86      inference('sup-', [status(thm)], ['61', '62'])).
% 0.67/0.86  thf('64', plain,
% 0.67/0.86      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86         = (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup+', [status(thm)], ['63', '64'])).
% 0.67/0.86  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('67', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('68', plain,
% 0.67/0.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.67/0.86         ((v1_relat_1 @ X7)
% 0.67/0.86          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.86  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.86      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.86  thf('70', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.86      inference('demod', [status(thm)],
% 0.67/0.86                ['39', '40', '51', '60', '65', '66', '69'])).
% 0.67/0.86  thf('71', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 0.67/0.86        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.86        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['2', '70'])).
% 0.67/0.86  thf('72', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup+', [status(thm)], ['63', '64'])).
% 0.67/0.86  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.86      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.86  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('75', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('76', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.67/0.86        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 0.67/0.86  thf('77', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['76'])).
% 0.67/0.86  thf('78', plain,
% 0.67/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.67/0.86      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.86  thf(d4_tops_2, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.86       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.67/0.86         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.67/0.86  thf('79', plain,
% 0.67/0.86      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.67/0.86         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.67/0.86          | ~ (v2_funct_1 @ X36)
% 0.67/0.86          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.67/0.86          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.67/0.86          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.67/0.86          | ~ (v1_funct_1 @ X36))),
% 0.67/0.86      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.67/0.86  thf('80', plain,
% 0.67/0.86      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.86             (k2_struct_0 @ sk_A))
% 0.67/0.86        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.86            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.86            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['78', '79'])).
% 0.67/0.86  thf('81', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.86      inference('simplify', [status(thm)], ['59'])).
% 0.67/0.86  thf('82', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.86      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.86  thf('83', plain,
% 0.67/0.86      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.86         (~ (v2_funct_1 @ X26)
% 0.67/0.86          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.67/0.86          | (v1_funct_2 @ (k2_funct_1 @ X26) @ X27 @ X28)
% 0.67/0.86          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.67/0.86          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.67/0.86          | ~ (v1_funct_1 @ X26))),
% 0.67/0.86      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.67/0.86  thf('84', plain,
% 0.67/0.86      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.86        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.86           (k2_struct_0 @ sk_A))
% 0.67/0.86        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86            != (k2_struct_0 @ sk_B))
% 0.67/0.86        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.86      inference('sup-', [status(thm)], ['82', '83'])).
% 0.67/0.86  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('86', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.86  thf('87', plain,
% 0.67/0.86      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86         = (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.86  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('89', plain,
% 0.67/0.86      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.86         (k2_struct_0 @ sk_A))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.67/0.86  thf('90', plain,
% 0.67/0.86      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.86        (k2_struct_0 @ sk_A))),
% 0.67/0.86      inference('simplify', [status(thm)], ['89'])).
% 0.67/0.86  thf('91', plain,
% 0.67/0.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.67/0.86      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.86  thf('92', plain,
% 0.67/0.86      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.67/0.86         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.67/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.67/0.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.67/0.86  thf('93', plain,
% 0.67/0.86      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.86         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['91', '92'])).
% 0.67/0.86  thf('94', plain,
% 0.67/0.86      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.86          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.67/0.86      inference('demod', [status(thm)], ['80', '81', '90', '93'])).
% 0.67/0.86  thf('95', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.67/0.86        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.86            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['77', '94'])).
% 0.67/0.86  thf('96', plain,
% 0.67/0.86      (![X5 : $i]:
% 0.67/0.86         (~ (v2_funct_1 @ X5)
% 0.67/0.86          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.67/0.86          | ~ (v1_funct_1 @ X5)
% 0.67/0.86          | ~ (v1_relat_1 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.86  thf('97', plain,
% 0.67/0.86      (![X5 : $i]:
% 0.67/0.86         (~ (v2_funct_1 @ X5)
% 0.67/0.86          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.67/0.86          | ~ (v1_funct_1 @ X5)
% 0.67/0.86          | ~ (v1_relat_1 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.86  thf('98', plain,
% 0.67/0.86      (![X6 : $i]:
% 0.67/0.86         (~ (v2_funct_1 @ X6)
% 0.67/0.86          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.67/0.86          | ~ (v1_funct_1 @ X6)
% 0.67/0.86          | ~ (v1_relat_1 @ X6))),
% 0.67/0.86      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.67/0.86  thf('99', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['76'])).
% 0.67/0.86  thf(dt_k2_funct_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.86       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.67/0.86         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.67/0.86  thf('100', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_relat_1 @ X0))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.67/0.86  thf('101', plain,
% 0.67/0.86      (![X5 : $i]:
% 0.67/0.86         (~ (v2_funct_1 @ X5)
% 0.67/0.86          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.67/0.86          | ~ (v1_funct_1 @ X5)
% 0.67/0.86          | ~ (v1_relat_1 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.86  thf('102', plain,
% 0.67/0.86      (![X6 : $i]:
% 0.67/0.86         (~ (v2_funct_1 @ X6)
% 0.67/0.86          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.67/0.86          | ~ (v1_funct_1 @ X6)
% 0.67/0.86          | ~ (v1_relat_1 @ X6))),
% 0.67/0.86      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.67/0.86  thf('103', plain,
% 0.67/0.86      (![X5 : $i]:
% 0.67/0.86         (~ (v2_funct_1 @ X5)
% 0.67/0.86          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.67/0.86          | ~ (v1_funct_1 @ X5)
% 0.67/0.86          | ~ (v1_relat_1 @ X5))),
% 0.67/0.86      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.86  thf(d4_partfun1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.67/0.86       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.67/0.86  thf('104', plain,
% 0.67/0.86      (![X16 : $i, X17 : $i]:
% 0.67/0.86         (((k1_relat_1 @ X17) != (X16))
% 0.67/0.86          | (v1_partfun1 @ X17 @ X16)
% 0.67/0.86          | ~ (v4_relat_1 @ X17 @ X16)
% 0.67/0.86          | ~ (v1_relat_1 @ X17))),
% 0.67/0.86      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.67/0.86  thf('105', plain,
% 0.67/0.86      (![X17 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ X17)
% 0.67/0.86          | ~ (v4_relat_1 @ X17 @ (k1_relat_1 @ X17))
% 0.67/0.86          | (v1_partfun1 @ X17 @ (k1_relat_1 @ X17)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['104'])).
% 0.67/0.86  thf('106', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.67/0.86          | ~ (v1_relat_1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ~ (v2_funct_1 @ X0)
% 0.67/0.86          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.67/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['103', '105'])).
% 0.67/0.86  thf('107', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.67/0.86          | ~ (v1_relat_1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ~ (v2_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.67/0.86          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.86             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.67/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['102', '106'])).
% 0.67/0.86  thf('108', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.67/0.86          | ~ (v1_relat_1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ~ (v2_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.86             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.67/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.67/0.86          | ~ (v2_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_relat_1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['101', '107'])).
% 0.67/0.86  thf('109', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.67/0.86          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.86             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.67/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v2_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_relat_1 @ X0)
% 0.67/0.86          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['108'])).
% 0.67/0.86  thf('110', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.67/0.86          | ~ (v1_relat_1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ~ (v2_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.86             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['100', '109'])).
% 0.67/0.86  thf('111', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.86           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.67/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v2_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_relat_1 @ X0)
% 0.67/0.86          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.67/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['110'])).
% 0.67/0.86  thf('112', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.67/0.86        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.86        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.67/0.86           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['99', '111'])).
% 0.67/0.86  thf('113', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.86      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.86  thf('114', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.86      inference('simplify', [status(thm)], ['59'])).
% 0.67/0.86  thf('115', plain,
% 0.67/0.86      (![X32 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('116', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(t132_funct_2, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( ( v1_funct_1 @ C ) & 
% 0.67/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.86       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.86           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.86         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.67/0.86           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.67/0.86  thf('117', plain,
% 0.67/0.86      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.67/0.86         (((X23) = (k1_xboole_0))
% 0.67/0.86          | ~ (v1_funct_1 @ X24)
% 0.67/0.86          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.67/0.86          | (v1_partfun1 @ X24 @ X25)
% 0.67/0.86          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.67/0.86          | ~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.67/0.86          | ~ (v1_funct_1 @ X24))),
% 0.67/0.86      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.67/0.86  thf('118', plain,
% 0.67/0.86      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.67/0.86         (~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.67/0.86          | (v1_partfun1 @ X24 @ X25)
% 0.67/0.86          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.67/0.86          | ~ (v1_funct_1 @ X24)
% 0.67/0.86          | ((X23) = (k1_xboole_0)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['117'])).
% 0.67/0.86  thf('119', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.67/0.86        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['116', '118'])).
% 0.67/0.86  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('121', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('122', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.67/0.86  thf('123', plain,
% 0.67/0.86      (![X16 : $i, X17 : $i]:
% 0.67/0.86         (~ (v1_partfun1 @ X17 @ X16)
% 0.67/0.86          | ((k1_relat_1 @ X17) = (X16))
% 0.67/0.86          | ~ (v4_relat_1 @ X17 @ X16)
% 0.67/0.86          | ~ (v1_relat_1 @ X17))),
% 0.67/0.86      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.67/0.86  thf('124', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.86        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.67/0.86        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['122', '123'])).
% 0.67/0.86  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.86      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.86  thf('126', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(cc2_relset_1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.86       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.67/0.86  thf('127', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.86         ((v4_relat_1 @ X10 @ X11)
% 0.67/0.86          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.67/0.86  thf('128', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['126', '127'])).
% 0.67/0.86  thf('129', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('demod', [status(thm)], ['124', '125', '128'])).
% 0.67/0.86  thf(fc2_struct_0, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.67/0.86       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.67/0.86  thf('130', plain,
% 0.67/0.86      (![X33 : $i]:
% 0.67/0.86         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 0.67/0.86          | ~ (l1_struct_0 @ X33)
% 0.67/0.86          | (v2_struct_0 @ X33))),
% 0.67/0.86      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.67/0.86  thf('131', plain,
% 0.67/0.86      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.86        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.67/0.86        | (v2_struct_0 @ sk_B)
% 0.67/0.86        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['129', '130'])).
% 0.67/0.86  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.67/0.86  thf('132', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.86      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.86  thf('133', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('134', plain,
% 0.67/0.86      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.67/0.86  thf('135', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('136', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('clc', [status(thm)], ['134', '135'])).
% 0.67/0.86  thf('137', plain,
% 0.67/0.86      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup+', [status(thm)], ['115', '136'])).
% 0.67/0.86  thf('138', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('139', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['137', '138'])).
% 0.67/0.86  thf('140', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.86  thf('141', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.86         ((v4_relat_1 @ X10 @ X11)
% 0.67/0.86          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.67/0.86  thf('142', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['140', '141'])).
% 0.67/0.86  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.86      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.86  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('146', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.67/0.86           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.67/0.86      inference('demod', [status(thm)],
% 0.67/0.86                ['112', '113', '114', '139', '142', '143', '144', '145'])).
% 0.67/0.86  thf('147', plain,
% 0.67/0.86      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.67/0.86        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup+', [status(thm)], ['98', '146'])).
% 0.67/0.86  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.86      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.86  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('151', plain,
% 0.67/0.86      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 0.67/0.86  thf('152', plain,
% 0.67/0.86      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup+', [status(thm)], ['97', '151'])).
% 0.67/0.86  thf('153', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.86      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.86  thf('154', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.86      inference('simplify', [status(thm)], ['59'])).
% 0.67/0.86  thf('155', plain,
% 0.67/0.86      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('demod', [status(thm)], ['152', '153', '154'])).
% 0.67/0.86  thf('156', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['76'])).
% 0.67/0.86  thf('157', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.86      inference('clc', [status(thm)], ['155', '156'])).
% 0.67/0.86  thf('158', plain,
% 0.67/0.86      (![X16 : $i, X17 : $i]:
% 0.67/0.86         (~ (v1_partfun1 @ X17 @ X16)
% 0.67/0.86          | ((k1_relat_1 @ X17) = (X16))
% 0.67/0.86          | ~ (v4_relat_1 @ X17 @ X16)
% 0.67/0.86          | ~ (v1_relat_1 @ X17))),
% 0.67/0.86      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.67/0.86  thf('159', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.86        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['157', '158'])).
% 0.67/0.86  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.86      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.86  thf('161', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['137', '138'])).
% 0.67/0.86  thf('162', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.86      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.67/0.86  thf('163', plain,
% 0.67/0.86      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.67/0.86        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.86        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['96', '162'])).
% 0.67/0.86  thf('164', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['137', '138'])).
% 0.67/0.86  thf('165', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['140', '141'])).
% 0.67/0.86  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.86      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.86  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('169', plain,
% 0.67/0.86      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('demod', [status(thm)],
% 0.67/0.86                ['163', '164', '165', '166', '167', '168'])).
% 0.67/0.86  thf('170', plain,
% 0.67/0.86      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.86          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('clc', [status(thm)], ['95', '169'])).
% 0.67/0.86  thf('171', plain,
% 0.67/0.86      (![X32 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('172', plain,
% 0.67/0.86      (![X32 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('173', plain,
% 0.67/0.86      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.86           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.86          sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('174', plain,
% 0.67/0.86      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.86            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.86           sk_C)
% 0.67/0.86        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['172', '173'])).
% 0.67/0.86  thf('175', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('176', plain,
% 0.67/0.86      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.86           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.86          sk_C)),
% 0.67/0.86      inference('demod', [status(thm)], ['174', '175'])).
% 0.67/0.86  thf('177', plain,
% 0.67/0.86      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.86            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.86           sk_C)
% 0.67/0.86        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['171', '176'])).
% 0.67/0.86  thf('178', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('179', plain,
% 0.67/0.86      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.86           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.86          sk_C)),
% 0.67/0.86      inference('demod', [status(thm)], ['177', '178'])).
% 0.67/0.86  thf('180', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('clc', [status(thm)], ['134', '135'])).
% 0.67/0.86  thf('181', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['137', '138'])).
% 0.67/0.86  thf('182', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['180', '181'])).
% 0.67/0.86  thf('183', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['180', '181'])).
% 0.67/0.86  thf('184', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['180', '181'])).
% 0.67/0.86  thf('185', plain,
% 0.67/0.86      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.86           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.86          sk_C)),
% 0.67/0.86      inference('demod', [status(thm)], ['179', '182', '183', '184'])).
% 0.67/0.86  thf('186', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.86      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.86  thf('187', plain,
% 0.67/0.86      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.67/0.86         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.67/0.86          | ~ (v2_funct_1 @ X36)
% 0.67/0.86          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.67/0.86          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.67/0.86          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.67/0.86          | ~ (v1_funct_1 @ X36))),
% 0.67/0.86      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.67/0.86  thf('188', plain,
% 0.67/0.86      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.86        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86            = (k2_funct_1 @ sk_C))
% 0.67/0.86        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.86        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86            != (k2_struct_0 @ sk_B)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['186', '187'])).
% 0.67/0.86  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('190', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.86  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('192', plain,
% 0.67/0.86      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86         = (k2_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.86  thf('193', plain,
% 0.67/0.86      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86          = (k2_funct_1 @ sk_C))
% 0.67/0.86        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['188', '189', '190', '191', '192'])).
% 0.67/0.86  thf('194', plain,
% 0.67/0.86      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.86         = (k2_funct_1 @ sk_C))),
% 0.67/0.86      inference('simplify', [status(thm)], ['193'])).
% 0.67/0.86  thf('195', plain,
% 0.67/0.86      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.86           (k2_funct_1 @ sk_C)) @ 
% 0.67/0.86          sk_C)),
% 0.67/0.86      inference('demod', [status(thm)], ['185', '194'])).
% 0.67/0.86  thf('196', plain,
% 0.67/0.86      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['170', '195'])).
% 0.67/0.86  thf('197', plain,
% 0.67/0.86      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.86           sk_C)
% 0.67/0.86        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.86        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['1', '196'])).
% 0.67/0.86  thf('198', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.86  thf('199', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_C @ 
% 0.67/0.86        (k1_zfmisc_1 @ 
% 0.67/0.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(reflexivity_r2_funct_2, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.67/0.86         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.67/0.86         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.86       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.67/0.86  thf('200', plain,
% 0.67/0.86      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.67/0.86         ((r2_funct_2 @ X19 @ X20 @ X21 @ X21)
% 0.67/0.86          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.67/0.86          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.67/0.86          | ~ (v1_funct_1 @ X21)
% 0.67/0.86          | ~ (v1_funct_1 @ X22)
% 0.67/0.86          | ~ (v1_funct_2 @ X22 @ X19 @ X20)
% 0.67/0.86          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.67/0.86      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.67/0.86  thf('201', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X0 @ 
% 0.67/0.86             (k1_zfmisc_1 @ 
% 0.67/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.67/0.86          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ sk_C)
% 0.67/0.86          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.86          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.86             sk_C))),
% 0.67/0.86      inference('sup-', [status(thm)], ['199', '200'])).
% 0.67/0.86  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('203', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('204', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X0 @ 
% 0.67/0.86             (k1_zfmisc_1 @ 
% 0.67/0.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.67/0.86          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.86             sk_C))),
% 0.67/0.86      inference('demod', [status(thm)], ['201', '202', '203'])).
% 0.67/0.86  thf('205', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['180', '181'])).
% 0.67/0.86  thf('206', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['180', '181'])).
% 0.67/0.86  thf('207', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['180', '181'])).
% 0.67/0.86  thf('208', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X0 @ 
% 0.67/0.86             (k1_zfmisc_1 @ 
% 0.67/0.86              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.67/0.86          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.86             sk_C))),
% 0.67/0.86      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 0.67/0.86  thf('209', plain,
% 0.67/0.86      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.67/0.86        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.86        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['198', '208'])).
% 0.67/0.86  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('211', plain,
% 0.67/0.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['29', '30'])).
% 0.67/0.86  thf('212', plain,
% 0.67/0.86      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.67/0.86      inference('demod', [status(thm)], ['209', '210', '211'])).
% 0.67/0.86  thf('213', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.86      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.86  thf('214', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('215', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('216', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.67/0.86      inference('demod', [status(thm)], ['197', '212', '213', '214', '215'])).
% 0.67/0.86  thf('217', plain,
% 0.67/0.86      (![X32 : $i]:
% 0.67/0.86         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.67/0.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.86  thf('218', plain,
% 0.67/0.86      (![X33 : $i]:
% 0.67/0.86         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 0.67/0.86          | ~ (l1_struct_0 @ X33)
% 0.67/0.86          | (v2_struct_0 @ X33))),
% 0.67/0.86      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.67/0.86  thf('219', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | (v2_struct_0 @ X0)
% 0.67/0.86          | ~ (l1_struct_0 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['217', '218'])).
% 0.67/0.86  thf('220', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((v2_struct_0 @ X0)
% 0.67/0.86          | ~ (l1_struct_0 @ X0)
% 0.67/0.86          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['219'])).
% 0.67/0.86  thf('221', plain,
% 0.67/0.86      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.86        | ~ (l1_struct_0 @ sk_B)
% 0.67/0.86        | (v2_struct_0 @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['216', '220'])).
% 0.67/0.86  thf('222', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.86      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.86  thf('223', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('224', plain, ((v2_struct_0 @ sk_B)),
% 0.67/0.86      inference('demod', [status(thm)], ['221', '222', '223'])).
% 0.67/0.86  thf('225', plain, ($false), inference('demod', [status(thm)], ['0', '224'])).
% 0.67/0.86  
% 0.67/0.86  % SZS output end Refutation
% 0.67/0.86  
% 0.67/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
