%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hM0c5VQv7A

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:15 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  273 (2022 expanded)
%              Number of leaves         :   48 ( 616 expanded)
%              Depth                    :   33
%              Number of atoms          : 2566 (43972 expanded)
%              Number of equality atoms :  140 (1319 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ( ( k5_relat_1 @ X31 @ ( k2_funct_1 @ X31 ) )
        = ( k6_partfun1 @ X32 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X32 @ X30 @ X31 )
       != X30 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('13',plain,(
    ! [X22: $i] :
      ( ( k6_partfun1 @ X22 )
      = ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ( ( k5_relat_1 @ X31 @ ( k2_funct_1 @ X31 ) )
        = ( k6_relat_1 @ X32 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X32 @ X30 @ X31 )
       != X30 ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('55',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('59',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('60',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('64',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('65',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40','53','62','67','68','73'])).

thf('75',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
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

thf('83',plain,(
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

thf('84',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['61'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('87',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X27 ) @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('91',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('92',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('96',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('97',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','94','97'])).

thf('99',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['81','98'])).

thf('100',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('101',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('102',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('103',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('104',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('106',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('107',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('108',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != X20 )
      | ( v1_partfun1 @ X21 @ X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('109',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v4_relat_1 @ X21 @ ( k1_relat_1 @ X21 ) )
      | ( v1_partfun1 @ X21 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','109'])).

thf('111',plain,(
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
    inference('sup-',[status(thm)],['106','110'])).

thf('112',plain,(
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
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
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
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
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
    inference('sup-',[status(thm)],['104','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['103','115'])).

thf('117',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['61'])).

thf('119',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
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

thf('121',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('122',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('127',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('130',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('131',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','131'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('133',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('134',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['119','138'])).

thf('140',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('143',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('144',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','141','144','145','146','147'])).

thf('149',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','153'])).

thf('155',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('156',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['61'])).

thf('157',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('159',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('161',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('163',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('164',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','164'])).

thf('166',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('167',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['165','166','167','168','169','170'])).

thf('172',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['99','171'])).

thf('173',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('174',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('175',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['173','178'])).

thf('180',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('183',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('184',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('186',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('187',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['181','184','185','186'])).

thf('188',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('189',plain,(
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

thf('190',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('193',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('195',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['190','191','192','193','194'])).

thf('196',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['187','196'])).

thf('198',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','197'])).

thf('199',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','198'])).

thf('200',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('201',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('202',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_funct_2 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['200','206'])).

thf('208',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('210',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('212',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['199','210','211','212','213'])).

thf('215',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('216',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['214','218'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('220',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('221',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    $false ),
    inference(demod,[status(thm)],['0','222'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hM0c5VQv7A
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:26:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.58/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.83  % Solved by: fo/fo7.sh
% 0.58/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.83  % done 628 iterations in 0.369s
% 0.58/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.83  % SZS output start Refutation
% 0.58/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.83  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.83  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.58/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.83  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.58/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.83  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.58/0.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.58/0.83  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.83  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.58/0.83  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.58/0.83  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.58/0.83  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.83  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.58/0.83  thf(t64_tops_2, conjecture,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( l1_struct_0 @ A ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.58/0.83           ( ![C:$i]:
% 0.58/0.83             ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.83                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.83                 ( m1_subset_1 @
% 0.58/0.83                   C @ 
% 0.58/0.83                   ( k1_zfmisc_1 @
% 0.58/0.83                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.83               ( ( ( ( k2_relset_1 @
% 0.58/0.83                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.58/0.83                     ( k2_struct_0 @ B ) ) & 
% 0.58/0.83                   ( v2_funct_1 @ C ) ) =>
% 0.58/0.83                 ( r2_funct_2 @
% 0.58/0.83                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.83                   ( k2_tops_2 @
% 0.58/0.83                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.58/0.83                     ( k2_tops_2 @
% 0.58/0.83                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.58/0.83                   C ) ) ) ) ) ) ))).
% 0.58/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.83    (~( ![A:$i]:
% 0.58/0.83        ( ( l1_struct_0 @ A ) =>
% 0.58/0.83          ( ![B:$i]:
% 0.58/0.83            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.58/0.83              ( ![C:$i]:
% 0.58/0.83                ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.83                    ( v1_funct_2 @
% 0.58/0.83                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.83                    ( m1_subset_1 @
% 0.67/0.83                      C @ 
% 0.67/0.83                      ( k1_zfmisc_1 @
% 0.67/0.83                        ( k2_zfmisc_1 @
% 0.67/0.83                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.67/0.83                  ( ( ( ( k2_relset_1 @
% 0.67/0.83                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.67/0.83                        ( k2_struct_0 @ B ) ) & 
% 0.67/0.83                      ( v2_funct_1 @ C ) ) =>
% 0.67/0.83                    ( r2_funct_2 @
% 0.67/0.83                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.67/0.83                      ( k2_tops_2 @
% 0.67/0.83                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.67/0.83                        ( k2_tops_2 @
% 0.67/0.83                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.67/0.83                      C ) ) ) ) ) ) ) )),
% 0.67/0.83    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.67/0.83  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf(t65_funct_1, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.83       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.67/0.83  thf('1', plain,
% 0.67/0.83      (![X10 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X10)
% 0.67/0.83          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.67/0.83          | ~ (v1_funct_1 @ X10)
% 0.67/0.83          | ~ (v1_relat_1 @ X10))),
% 0.67/0.83      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.67/0.83  thf(t55_funct_1, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.83       ( ( v2_funct_1 @ A ) =>
% 0.67/0.83         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.67/0.83           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.67/0.83  thf('2', plain,
% 0.67/0.83      (![X9 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X9)
% 0.67/0.83          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.67/0.83          | ~ (v1_funct_1 @ X9)
% 0.67/0.83          | ~ (v1_relat_1 @ X9))),
% 0.67/0.83      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.83  thf(d3_struct_0, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.67/0.83  thf('3', plain,
% 0.67/0.83      (![X33 : $i]:
% 0.67/0.83         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.83  thf('4', plain,
% 0.67/0.83      (![X33 : $i]:
% 0.67/0.83         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.83  thf('5', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('6', plain,
% 0.67/0.83      (((m1_subset_1 @ sk_C @ 
% 0.67/0.83         (k1_zfmisc_1 @ 
% 0.67/0.83          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.67/0.83        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.83      inference('sup+', [status(thm)], ['4', '5'])).
% 0.67/0.83  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('8', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.83      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.83  thf('9', plain,
% 0.67/0.83      (((m1_subset_1 @ sk_C @ 
% 0.67/0.83         (k1_zfmisc_1 @ 
% 0.67/0.83          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.67/0.83        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup+', [status(thm)], ['3', '8'])).
% 0.67/0.83  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('11', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.83      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.83  thf(t35_funct_2, axiom,
% 0.67/0.83    (![A:$i,B:$i,C:$i]:
% 0.67/0.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.83       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.67/0.83         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.67/0.83           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.67/0.83             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.67/0.83  thf('12', plain,
% 0.67/0.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.67/0.83         (((X30) = (k1_xboole_0))
% 0.67/0.83          | ~ (v1_funct_1 @ X31)
% 0.67/0.83          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 0.67/0.83          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 0.67/0.83          | ((k5_relat_1 @ X31 @ (k2_funct_1 @ X31)) = (k6_partfun1 @ X32))
% 0.67/0.83          | ~ (v2_funct_1 @ X31)
% 0.67/0.83          | ((k2_relset_1 @ X32 @ X30 @ X31) != (X30)))),
% 0.67/0.83      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.67/0.83  thf(redefinition_k6_partfun1, axiom,
% 0.67/0.83    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.67/0.83  thf('13', plain, (![X22 : $i]: ((k6_partfun1 @ X22) = (k6_relat_1 @ X22))),
% 0.67/0.83      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.83  thf('14', plain,
% 0.67/0.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.67/0.83         (((X30) = (k1_xboole_0))
% 0.67/0.83          | ~ (v1_funct_1 @ X31)
% 0.67/0.83          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 0.67/0.83          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 0.67/0.83          | ((k5_relat_1 @ X31 @ (k2_funct_1 @ X31)) = (k6_relat_1 @ X32))
% 0.67/0.83          | ~ (v2_funct_1 @ X31)
% 0.67/0.83          | ((k2_relset_1 @ X32 @ X30 @ X31) != (X30)))),
% 0.67/0.83      inference('demod', [status(thm)], ['12', '13'])).
% 0.67/0.83  thf('15', plain,
% 0.67/0.83      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83          != (k2_struct_0 @ sk_B))
% 0.67/0.83        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.83        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.67/0.83            = (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.67/0.83        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.83        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['11', '14'])).
% 0.67/0.83  thf('16', plain,
% 0.67/0.83      (![X33 : $i]:
% 0.67/0.83         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.83  thf('17', plain,
% 0.67/0.83      (![X33 : $i]:
% 0.67/0.83         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.83  thf('18', plain,
% 0.67/0.83      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83         = (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('19', plain,
% 0.67/0.83      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83          = (k2_struct_0 @ sk_B))
% 0.67/0.83        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.83      inference('sup+', [status(thm)], ['17', '18'])).
% 0.67/0.83  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('21', plain,
% 0.67/0.83      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83         = (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.83  thf('22', plain,
% 0.67/0.83      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83          = (k2_struct_0 @ sk_B))
% 0.67/0.83        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup+', [status(thm)], ['16', '21'])).
% 0.67/0.83  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('24', plain,
% 0.67/0.83      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83         = (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.83  thf('25', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('26', plain,
% 0.67/0.83      (![X33 : $i]:
% 0.67/0.83         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.83  thf('27', plain,
% 0.67/0.83      (![X33 : $i]:
% 0.67/0.83         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.83  thf('28', plain,
% 0.67/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('29', plain,
% 0.67/0.83      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.83        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.83      inference('sup+', [status(thm)], ['27', '28'])).
% 0.67/0.83  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('31', plain,
% 0.67/0.83      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['29', '30'])).
% 0.67/0.83  thf('32', plain,
% 0.67/0.83      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.83        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup+', [status(thm)], ['26', '31'])).
% 0.67/0.83  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('34', plain,
% 0.67/0.83      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.83  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('36', plain,
% 0.67/0.83      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.67/0.83        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.67/0.83            = (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.67/0.83        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.83      inference('demod', [status(thm)], ['15', '24', '25', '34', '35'])).
% 0.67/0.83  thf('37', plain,
% 0.67/0.83      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.83        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.67/0.83            = (k6_relat_1 @ (k2_struct_0 @ sk_A))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['36'])).
% 0.67/0.83  thf(t48_funct_1, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.83       ( ![B:$i]:
% 0.67/0.83         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.67/0.83           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.67/0.83               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.67/0.83             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.67/0.83  thf('38', plain,
% 0.67/0.83      (![X7 : $i, X8 : $i]:
% 0.67/0.83         (~ (v1_relat_1 @ X7)
% 0.67/0.83          | ~ (v1_funct_1 @ X7)
% 0.67/0.83          | (v2_funct_1 @ X8)
% 0.67/0.83          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.67/0.83          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.67/0.83          | ~ (v1_funct_1 @ X8)
% 0.67/0.83          | ~ (v1_relat_1 @ X8))),
% 0.67/0.83      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.67/0.83  thf('39', plain,
% 0.67/0.83      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.67/0.83        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.83        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.83        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.83        | ~ (v1_relat_1 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.83  thf(fc4_funct_1, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.67/0.83       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.67/0.83  thf('40', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.67/0.83      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.67/0.83  thf('41', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.83      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.83  thf(t31_funct_2, axiom,
% 0.67/0.83    (![A:$i,B:$i,C:$i]:
% 0.67/0.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.83       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.67/0.83         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.67/0.83           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.67/0.83           ( m1_subset_1 @
% 0.67/0.83             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.67/0.83  thf('42', plain,
% 0.67/0.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X27)
% 0.67/0.83          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.67/0.83          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 0.67/0.83             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.67/0.83          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.67/0.83          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.67/0.83          | ~ (v1_funct_1 @ X27))),
% 0.67/0.83      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.67/0.83  thf('43', plain,
% 0.67/0.83      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.83        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.83        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.83           (k1_zfmisc_1 @ 
% 0.67/0.83            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.67/0.83        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83            != (k2_struct_0 @ sk_B))
% 0.67/0.83        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.83  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('45', plain,
% 0.67/0.83      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.83  thf('46', plain,
% 0.67/0.83      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83         = (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.83  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('48', plain,
% 0.67/0.83      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.83         (k1_zfmisc_1 @ 
% 0.67/0.83          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.67/0.83        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.67/0.83      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.67/0.83  thf('49', plain,
% 0.67/0.83      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.83  thf(cc2_relat_1, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( v1_relat_1 @ A ) =>
% 0.67/0.83       ( ![B:$i]:
% 0.67/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.67/0.83  thf('50', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.67/0.83          | (v1_relat_1 @ X0)
% 0.67/0.83          | ~ (v1_relat_1 @ X1))),
% 0.67/0.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.67/0.83  thf('51', plain,
% 0.67/0.83      ((~ (v1_relat_1 @ 
% 0.67/0.83           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 0.67/0.83        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.83  thf(fc6_relat_1, axiom,
% 0.67/0.83    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.67/0.83  thf('52', plain,
% 0.67/0.83      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.67/0.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.67/0.83  thf('53', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.83      inference('demod', [status(thm)], ['51', '52'])).
% 0.67/0.83  thf('54', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.83      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.83  thf('55', plain,
% 0.67/0.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X27)
% 0.67/0.83          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.67/0.83          | (v1_funct_1 @ (k2_funct_1 @ X27))
% 0.67/0.83          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.67/0.83          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.67/0.83          | ~ (v1_funct_1 @ X27))),
% 0.67/0.83      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.67/0.83  thf('56', plain,
% 0.67/0.83      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.83        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.83        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83            != (k2_struct_0 @ sk_B))
% 0.67/0.83        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.83  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('58', plain,
% 0.67/0.83      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.83  thf('59', plain,
% 0.67/0.83      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83         = (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.83  thf('60', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('61', plain,
% 0.67/0.83      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.67/0.83      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.67/0.83  thf('62', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.83      inference('simplify', [status(thm)], ['61'])).
% 0.67/0.83  thf('63', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf(redefinition_k2_relset_1, axiom,
% 0.67/0.83    (![A:$i,B:$i,C:$i]:
% 0.67/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.83       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.67/0.83  thf('64', plain,
% 0.67/0.83      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.67/0.83         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.67/0.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.67/0.83      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.67/0.83  thf('65', plain,
% 0.67/0.83      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83         = (k2_relat_1 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['63', '64'])).
% 0.67/0.83  thf('66', plain,
% 0.67/0.83      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83         = (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('67', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup+', [status(thm)], ['65', '66'])).
% 0.67/0.83  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('69', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('70', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.67/0.83          | (v1_relat_1 @ X0)
% 0.67/0.83          | ~ (v1_relat_1 @ X1))),
% 0.67/0.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.67/0.83  thf('71', plain,
% 0.67/0.83      ((~ (v1_relat_1 @ 
% 0.67/0.83           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.67/0.83        | (v1_relat_1 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['69', '70'])).
% 0.67/0.83  thf('72', plain,
% 0.67/0.83      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.67/0.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.67/0.83  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.83      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.83  thf('74', plain,
% 0.67/0.83      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.83        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.83        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.83      inference('demod', [status(thm)],
% 0.67/0.83                ['39', '40', '53', '62', '67', '68', '73'])).
% 0.67/0.83  thf('75', plain,
% 0.67/0.83      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 0.67/0.83        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.83        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.83        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['2', '74'])).
% 0.67/0.83  thf('76', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('sup+', [status(thm)], ['65', '66'])).
% 0.67/0.83  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.83      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.83  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('79', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('80', plain,
% 0.67/0.83      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.67/0.83        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.83      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.67/0.83  thf('81', plain,
% 0.67/0.83      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.83        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.83      inference('simplify', [status(thm)], ['80'])).
% 0.67/0.83  thf('82', plain,
% 0.67/0.83      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.83  thf(d4_tops_2, axiom,
% 0.67/0.83    (![A:$i,B:$i,C:$i]:
% 0.67/0.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.83       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.67/0.83         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.67/0.83  thf('83', plain,
% 0.67/0.83      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.67/0.83         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 0.67/0.83          | ~ (v2_funct_1 @ X37)
% 0.67/0.83          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 0.67/0.83          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.67/0.83          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.67/0.83          | ~ (v1_funct_1 @ X37))),
% 0.67/0.83      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.67/0.83  thf('84', plain,
% 0.67/0.83      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.83             (k2_struct_0 @ sk_A))
% 0.67/0.83        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.83            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.83        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.83            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['82', '83'])).
% 0.67/0.83  thf('85', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.83      inference('simplify', [status(thm)], ['61'])).
% 0.67/0.83  thf('86', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.83      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.83  thf('87', plain,
% 0.67/0.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X27)
% 0.67/0.83          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.67/0.83          | (v1_funct_2 @ (k2_funct_1 @ X27) @ X28 @ X29)
% 0.67/0.83          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.67/0.83          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.67/0.83          | ~ (v1_funct_1 @ X27))),
% 0.67/0.83      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.67/0.83  thf('88', plain,
% 0.67/0.83      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.83        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.83        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.83           (k2_struct_0 @ sk_A))
% 0.67/0.83        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83            != (k2_struct_0 @ sk_B))
% 0.67/0.83        | ~ (v2_funct_1 @ sk_C))),
% 0.67/0.83      inference('sup-', [status(thm)], ['86', '87'])).
% 0.67/0.83  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('90', plain,
% 0.67/0.83      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.83  thf('91', plain,
% 0.67/0.83      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.83         = (k2_struct_0 @ sk_B))),
% 0.67/0.83      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.83  thf('92', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('93', plain,
% 0.67/0.83      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.83         (k2_struct_0 @ sk_A))
% 0.67/0.83        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.67/0.83      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.67/0.83  thf('94', plain,
% 0.67/0.83      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.83        (k2_struct_0 @ sk_A))),
% 0.67/0.83      inference('simplify', [status(thm)], ['93'])).
% 0.67/0.83  thf('95', plain,
% 0.67/0.83      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.67/0.83      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.83  thf('96', plain,
% 0.67/0.83      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.67/0.83         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.67/0.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.67/0.83      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.67/0.83  thf('97', plain,
% 0.67/0.83      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.83         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['95', '96'])).
% 0.67/0.83  thf('98', plain,
% 0.67/0.83      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.83          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.83        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.67/0.83      inference('demod', [status(thm)], ['84', '85', '94', '97'])).
% 0.67/0.83  thf('99', plain,
% 0.67/0.83      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.83        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.67/0.83        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.83            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['81', '98'])).
% 0.67/0.83  thf('100', plain,
% 0.67/0.83      (![X9 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X9)
% 0.67/0.83          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.67/0.83          | ~ (v1_funct_1 @ X9)
% 0.67/0.83          | ~ (v1_relat_1 @ X9))),
% 0.67/0.83      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.83  thf('101', plain,
% 0.67/0.83      (![X9 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X9)
% 0.67/0.83          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.67/0.83          | ~ (v1_funct_1 @ X9)
% 0.67/0.83          | ~ (v1_relat_1 @ X9))),
% 0.67/0.83      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.83  thf('102', plain,
% 0.67/0.83      (![X10 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X10)
% 0.67/0.83          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.67/0.83          | ~ (v1_funct_1 @ X10)
% 0.67/0.83          | ~ (v1_relat_1 @ X10))),
% 0.67/0.83      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.67/0.83  thf('103', plain,
% 0.67/0.83      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.83        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.83      inference('simplify', [status(thm)], ['80'])).
% 0.67/0.83  thf(dt_k2_funct_1, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.83       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.67/0.83         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.67/0.83  thf('104', plain,
% 0.67/0.83      (![X4 : $i]:
% 0.67/0.83         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.67/0.83          | ~ (v1_funct_1 @ X4)
% 0.67/0.83          | ~ (v1_relat_1 @ X4))),
% 0.67/0.83      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.67/0.83  thf('105', plain,
% 0.67/0.83      (![X9 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X9)
% 0.67/0.83          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.67/0.83          | ~ (v1_funct_1 @ X9)
% 0.67/0.83          | ~ (v1_relat_1 @ X9))),
% 0.67/0.83      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.83  thf('106', plain,
% 0.67/0.83      (![X10 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X10)
% 0.67/0.83          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.67/0.83          | ~ (v1_funct_1 @ X10)
% 0.67/0.83          | ~ (v1_relat_1 @ X10))),
% 0.67/0.83      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.67/0.83  thf('107', plain,
% 0.67/0.83      (![X9 : $i]:
% 0.67/0.83         (~ (v2_funct_1 @ X9)
% 0.67/0.83          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.67/0.83          | ~ (v1_funct_1 @ X9)
% 0.67/0.83          | ~ (v1_relat_1 @ X9))),
% 0.67/0.83      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.67/0.83  thf(d4_partfun1, axiom,
% 0.67/0.83    (![A:$i,B:$i]:
% 0.67/0.83     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.67/0.83       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.67/0.83  thf('108', plain,
% 0.67/0.83      (![X20 : $i, X21 : $i]:
% 0.67/0.83         (((k1_relat_1 @ X21) != (X20))
% 0.67/0.83          | (v1_partfun1 @ X21 @ X20)
% 0.67/0.83          | ~ (v4_relat_1 @ X21 @ X20)
% 0.67/0.83          | ~ (v1_relat_1 @ X21))),
% 0.67/0.83      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.67/0.83  thf('109', plain,
% 0.67/0.83      (![X21 : $i]:
% 0.67/0.83         (~ (v1_relat_1 @ X21)
% 0.67/0.83          | ~ (v4_relat_1 @ X21 @ (k1_relat_1 @ X21))
% 0.67/0.83          | (v1_partfun1 @ X21 @ (k1_relat_1 @ X21)))),
% 0.67/0.83      inference('simplify', [status(thm)], ['108'])).
% 0.67/0.83  thf('110', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.67/0.83          | ~ (v1_relat_1 @ X0)
% 0.67/0.83          | ~ (v1_funct_1 @ X0)
% 0.67/0.83          | ~ (v2_funct_1 @ X0)
% 0.67/0.83          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.67/0.83          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['107', '109'])).
% 0.67/0.83  thf('111', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.67/0.83          | ~ (v1_relat_1 @ X0)
% 0.67/0.83          | ~ (v1_funct_1 @ X0)
% 0.67/0.83          | ~ (v2_funct_1 @ X0)
% 0.67/0.83          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.67/0.83          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.83             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.67/0.83          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['106', '110'])).
% 0.67/0.83  thf('112', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.67/0.83          | ~ (v1_relat_1 @ X0)
% 0.67/0.83          | ~ (v1_funct_1 @ X0)
% 0.67/0.83          | ~ (v2_funct_1 @ X0)
% 0.67/0.83          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.83             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.67/0.83          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.67/0.83          | ~ (v2_funct_1 @ X0)
% 0.67/0.83          | ~ (v1_funct_1 @ X0)
% 0.67/0.83          | ~ (v1_relat_1 @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['105', '111'])).
% 0.67/0.83  thf('113', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.67/0.83          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.83             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.67/0.83          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v2_funct_1 @ X0)
% 0.67/0.83          | ~ (v1_funct_1 @ X0)
% 0.67/0.83          | ~ (v1_relat_1 @ X0)
% 0.67/0.83          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.67/0.83      inference('simplify', [status(thm)], ['112'])).
% 0.67/0.83  thf('114', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.67/0.83          | ~ (v1_relat_1 @ X0)
% 0.67/0.83          | ~ (v1_funct_1 @ X0)
% 0.67/0.83          | ~ (v2_funct_1 @ X0)
% 0.67/0.83          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.83             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['104', '113'])).
% 0.67/0.83  thf('115', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.67/0.83           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.67/0.83          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v2_funct_1 @ X0)
% 0.67/0.83          | ~ (v1_funct_1 @ X0)
% 0.67/0.83          | ~ (v1_relat_1 @ X0)
% 0.67/0.83          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.67/0.83          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.67/0.83          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.67/0.83      inference('simplify', [status(thm)], ['114'])).
% 0.67/0.83  thf('116', plain,
% 0.67/0.83      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.83        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.83        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.67/0.83        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.83        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.83        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.67/0.83           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['103', '115'])).
% 0.67/0.83  thf('117', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.83      inference('demod', [status(thm)], ['51', '52'])).
% 0.67/0.83  thf('118', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.83      inference('simplify', [status(thm)], ['61'])).
% 0.67/0.83  thf('119', plain,
% 0.67/0.83      (![X33 : $i]:
% 0.67/0.83         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.83  thf('120', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf(cc5_funct_2, axiom,
% 0.67/0.83    (![A:$i,B:$i]:
% 0.67/0.83     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.67/0.83       ( ![C:$i]:
% 0.67/0.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.83           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.67/0.83             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.67/0.83  thf('121', plain,
% 0.67/0.83      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.67/0.83          | (v1_partfun1 @ X17 @ X18)
% 0.67/0.83          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.67/0.83          | ~ (v1_funct_1 @ X17)
% 0.67/0.83          | (v1_xboole_0 @ X19))),
% 0.67/0.83      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.67/0.83  thf('122', plain,
% 0.67/0.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.83        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['120', '121'])).
% 0.67/0.83  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('124', plain,
% 0.67/0.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('125', plain,
% 0.67/0.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.67/0.83      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.67/0.83  thf('126', plain,
% 0.67/0.83      (![X20 : $i, X21 : $i]:
% 0.67/0.83         (~ (v1_partfun1 @ X21 @ X20)
% 0.67/0.83          | ((k1_relat_1 @ X21) = (X20))
% 0.67/0.83          | ~ (v4_relat_1 @ X21 @ X20)
% 0.67/0.83          | ~ (v1_relat_1 @ X21))),
% 0.67/0.83      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.67/0.83  thf('127', plain,
% 0.67/0.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.83        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.67/0.83        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['125', '126'])).
% 0.67/0.83  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.83      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.83  thf('129', plain,
% 0.67/0.83      ((m1_subset_1 @ sk_C @ 
% 0.67/0.83        (k1_zfmisc_1 @ 
% 0.67/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf(cc2_relset_1, axiom,
% 0.67/0.83    (![A:$i,B:$i,C:$i]:
% 0.67/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.67/0.83  thf('130', plain,
% 0.67/0.83      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.67/0.83         ((v4_relat_1 @ X11 @ X12)
% 0.67/0.83          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.67/0.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.67/0.83  thf('131', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.67/0.83      inference('sup-', [status(thm)], ['129', '130'])).
% 0.67/0.83  thf('132', plain,
% 0.67/0.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.67/0.83        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.67/0.83      inference('demod', [status(thm)], ['127', '128', '131'])).
% 0.67/0.83  thf(fc2_struct_0, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.67/0.83       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.67/0.83  thf('133', plain,
% 0.67/0.83      (![X34 : $i]:
% 0.67/0.83         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 0.67/0.83          | ~ (l1_struct_0 @ X34)
% 0.67/0.83          | (v2_struct_0 @ X34))),
% 0.67/0.83      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.67/0.83  thf('134', plain,
% 0.67/0.83      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.67/0.84        | (v2_struct_0 @ sk_B)
% 0.67/0.84        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.84      inference('sup-', [status(thm)], ['132', '133'])).
% 0.67/0.84  thf('135', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('136', plain,
% 0.67/0.84      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.67/0.84      inference('demod', [status(thm)], ['134', '135'])).
% 0.67/0.84  thf('137', plain, (~ (v2_struct_0 @ sk_B)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('138', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.67/0.84      inference('clc', [status(thm)], ['136', '137'])).
% 0.67/0.84  thf('139', plain,
% 0.67/0.84      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.84      inference('sup+', [status(thm)], ['119', '138'])).
% 0.67/0.84  thf('140', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('141', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.84      inference('demod', [status(thm)], ['139', '140'])).
% 0.67/0.84  thf('142', plain,
% 0.67/0.84      ((m1_subset_1 @ sk_C @ 
% 0.67/0.84        (k1_zfmisc_1 @ 
% 0.67/0.84         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.84      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.84  thf('143', plain,
% 0.67/0.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.67/0.84         ((v4_relat_1 @ X11 @ X12)
% 0.67/0.84          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.67/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.67/0.84  thf('144', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.67/0.84      inference('sup-', [status(thm)], ['142', '143'])).
% 0.67/0.84  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.84  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('148', plain,
% 0.67/0.84      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.84        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.67/0.84           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.67/0.84      inference('demod', [status(thm)],
% 0.67/0.84                ['116', '117', '118', '141', '144', '145', '146', '147'])).
% 0.67/0.84  thf('149', plain,
% 0.67/0.84      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.67/0.84        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.84        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.84        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.84      inference('sup+', [status(thm)], ['102', '148'])).
% 0.67/0.84  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.84  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('153', plain,
% 0.67/0.84      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.67/0.84        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.84      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 0.67/0.84  thf('154', plain,
% 0.67/0.84      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.84        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.84        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.84        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.84        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.84      inference('sup+', [status(thm)], ['101', '153'])).
% 0.67/0.84  thf('155', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.84      inference('demod', [status(thm)], ['51', '52'])).
% 0.67/0.84  thf('156', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.67/0.84      inference('simplify', [status(thm)], ['61'])).
% 0.67/0.84  thf('157', plain,
% 0.67/0.84      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.84        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.67/0.84        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.84      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.67/0.84  thf('158', plain,
% 0.67/0.84      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.84        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.67/0.84      inference('simplify', [status(thm)], ['80'])).
% 0.67/0.84  thf('159', plain,
% 0.67/0.84      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.84        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.84      inference('clc', [status(thm)], ['157', '158'])).
% 0.67/0.84  thf('160', plain,
% 0.67/0.84      (![X20 : $i, X21 : $i]:
% 0.67/0.84         (~ (v1_partfun1 @ X21 @ X20)
% 0.67/0.84          | ((k1_relat_1 @ X21) = (X20))
% 0.67/0.84          | ~ (v4_relat_1 @ X21 @ X20)
% 0.67/0.84          | ~ (v1_relat_1 @ X21))),
% 0.67/0.84      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.67/0.84  thf('161', plain,
% 0.67/0.84      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.84        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.84        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.84        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.84      inference('sup-', [status(thm)], ['159', '160'])).
% 0.67/0.84  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.84  thf('163', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.84      inference('demod', [status(thm)], ['139', '140'])).
% 0.67/0.84  thf('164', plain,
% 0.67/0.84      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.84        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.84        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.67/0.84      inference('demod', [status(thm)], ['161', '162', '163'])).
% 0.67/0.84  thf('165', plain,
% 0.67/0.84      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.67/0.84        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.84        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.84        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.84        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.84      inference('sup-', [status(thm)], ['100', '164'])).
% 0.67/0.84  thf('166', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.84      inference('demod', [status(thm)], ['139', '140'])).
% 0.67/0.84  thf('167', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.67/0.84      inference('sup-', [status(thm)], ['142', '143'])).
% 0.67/0.84  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.84  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('171', plain,
% 0.67/0.84      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.84        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.84      inference('demod', [status(thm)],
% 0.67/0.84                ['165', '166', '167', '168', '169', '170'])).
% 0.67/0.84  thf('172', plain,
% 0.67/0.84      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.84          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.67/0.84        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.84      inference('clc', [status(thm)], ['99', '171'])).
% 0.67/0.84  thf('173', plain,
% 0.67/0.84      (![X33 : $i]:
% 0.67/0.84         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.84  thf('174', plain,
% 0.67/0.84      (![X33 : $i]:
% 0.67/0.84         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.84  thf('175', plain,
% 0.67/0.84      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.84          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.84           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.84          sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('176', plain,
% 0.67/0.84      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.84           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.84           sk_C)
% 0.67/0.84        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.84      inference('sup-', [status(thm)], ['174', '175'])).
% 0.67/0.84  thf('177', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('178', plain,
% 0.67/0.84      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.84          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.84           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.84          sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['176', '177'])).
% 0.67/0.84  thf('179', plain,
% 0.67/0.84      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.84           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.84            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.84           sk_C)
% 0.67/0.84        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.84      inference('sup-', [status(thm)], ['173', '178'])).
% 0.67/0.84  thf('180', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('181', plain,
% 0.67/0.84      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.84          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.84           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.84          sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['179', '180'])).
% 0.67/0.84  thf('182', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.67/0.84      inference('clc', [status(thm)], ['136', '137'])).
% 0.67/0.84  thf('183', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.84      inference('demod', [status(thm)], ['139', '140'])).
% 0.67/0.84  thf('184', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.67/0.84      inference('demod', [status(thm)], ['182', '183'])).
% 0.67/0.84  thf('185', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.67/0.84      inference('demod', [status(thm)], ['182', '183'])).
% 0.67/0.84  thf('186', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.67/0.84      inference('demod', [status(thm)], ['182', '183'])).
% 0.67/0.84  thf('187', plain,
% 0.67/0.84      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.84          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.84           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.67/0.84          sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['181', '184', '185', '186'])).
% 0.67/0.84  thf('188', plain,
% 0.67/0.84      ((m1_subset_1 @ sk_C @ 
% 0.67/0.84        (k1_zfmisc_1 @ 
% 0.67/0.84         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.84      inference('demod', [status(thm)], ['9', '10'])).
% 0.67/0.84  thf('189', plain,
% 0.67/0.84      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.67/0.84         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 0.67/0.84          | ~ (v2_funct_1 @ X37)
% 0.67/0.84          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 0.67/0.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.67/0.84          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.67/0.84          | ~ (v1_funct_1 @ X37))),
% 0.67/0.84      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.67/0.84  thf('190', plain,
% 0.67/0.84      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.84        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.84        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.84            = (k2_funct_1 @ sk_C))
% 0.67/0.84        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.84        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.84            != (k2_struct_0 @ sk_B)))),
% 0.67/0.84      inference('sup-', [status(thm)], ['188', '189'])).
% 0.67/0.84  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('192', plain,
% 0.67/0.84      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.67/0.84      inference('demod', [status(thm)], ['32', '33'])).
% 0.67/0.84  thf('193', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('194', plain,
% 0.67/0.84      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.84         = (k2_struct_0 @ sk_B))),
% 0.67/0.84      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.84  thf('195', plain,
% 0.67/0.84      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.84          = (k2_funct_1 @ sk_C))
% 0.67/0.84        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.67/0.84      inference('demod', [status(thm)], ['190', '191', '192', '193', '194'])).
% 0.67/0.84  thf('196', plain,
% 0.67/0.84      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.84         = (k2_funct_1 @ sk_C))),
% 0.67/0.84      inference('simplify', [status(thm)], ['195'])).
% 0.67/0.84  thf('197', plain,
% 0.67/0.84      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.84          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.67/0.84           (k2_funct_1 @ sk_C)) @ 
% 0.67/0.84          sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['187', '196'])).
% 0.67/0.84  thf('198', plain,
% 0.67/0.84      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.84           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 0.67/0.84        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.84      inference('sup-', [status(thm)], ['172', '197'])).
% 0.67/0.84  thf('199', plain,
% 0.67/0.84      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.84           sk_C)
% 0.67/0.84        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.84        | ~ (v2_funct_1 @ sk_C)
% 0.67/0.84        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.84      inference('sup-', [status(thm)], ['1', '198'])).
% 0.67/0.84  thf('200', plain,
% 0.67/0.84      ((m1_subset_1 @ sk_C @ 
% 0.67/0.84        (k1_zfmisc_1 @ 
% 0.67/0.84         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.84      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.84  thf('201', plain,
% 0.67/0.84      ((m1_subset_1 @ sk_C @ 
% 0.67/0.84        (k1_zfmisc_1 @ 
% 0.67/0.84         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.84      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.84  thf(reflexivity_r2_funct_2, axiom,
% 0.67/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.67/0.84         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.67/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.84       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.67/0.84  thf('202', plain,
% 0.67/0.84      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.67/0.84         ((r2_funct_2 @ X23 @ X24 @ X25 @ X25)
% 0.67/0.84          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.67/0.84          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.67/0.84          | ~ (v1_funct_1 @ X25)
% 0.67/0.84          | ~ (v1_funct_1 @ X26)
% 0.67/0.84          | ~ (v1_funct_2 @ X26 @ X23 @ X24)
% 0.67/0.84          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.67/0.84      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.67/0.84  thf('203', plain,
% 0.67/0.84      (![X0 : $i]:
% 0.67/0.84         (~ (m1_subset_1 @ X0 @ 
% 0.67/0.84             (k1_zfmisc_1 @ 
% 0.67/0.84              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.67/0.84          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.84          | ~ (v1_funct_1 @ X0)
% 0.67/0.84          | ~ (v1_funct_1 @ sk_C)
% 0.67/0.84          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.84          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.84             sk_C))),
% 0.67/0.84      inference('sup-', [status(thm)], ['201', '202'])).
% 0.67/0.84  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('205', plain,
% 0.67/0.84      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.84      inference('demod', [status(thm)], ['29', '30'])).
% 0.67/0.84  thf('206', plain,
% 0.67/0.84      (![X0 : $i]:
% 0.67/0.84         (~ (m1_subset_1 @ X0 @ 
% 0.67/0.84             (k1_zfmisc_1 @ 
% 0.67/0.84              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.67/0.84          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.84          | ~ (v1_funct_1 @ X0)
% 0.67/0.84          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.84             sk_C))),
% 0.67/0.84      inference('demod', [status(thm)], ['203', '204', '205'])).
% 0.67/0.84  thf('207', plain,
% 0.67/0.84      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.67/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.84        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.67/0.84      inference('sup-', [status(thm)], ['200', '206'])).
% 0.67/0.84  thf('208', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('209', plain,
% 0.67/0.84      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.84      inference('demod', [status(thm)], ['29', '30'])).
% 0.67/0.84  thf('210', plain,
% 0.67/0.84      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['207', '208', '209'])).
% 0.67/0.84  thf('211', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.84      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.84  thf('212', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('213', plain, ((v2_funct_1 @ sk_C)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('214', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.67/0.84      inference('demod', [status(thm)], ['199', '210', '211', '212', '213'])).
% 0.67/0.84  thf('215', plain,
% 0.67/0.84      (![X33 : $i]:
% 0.67/0.84         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.67/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.84  thf('216', plain,
% 0.67/0.84      (![X34 : $i]:
% 0.67/0.84         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 0.67/0.84          | ~ (l1_struct_0 @ X34)
% 0.67/0.84          | (v2_struct_0 @ X34))),
% 0.67/0.84      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.67/0.84  thf('217', plain,
% 0.67/0.84      (![X0 : $i]:
% 0.67/0.84         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.67/0.84          | ~ (l1_struct_0 @ X0)
% 0.67/0.84          | (v2_struct_0 @ X0)
% 0.67/0.84          | ~ (l1_struct_0 @ X0))),
% 0.67/0.84      inference('sup-', [status(thm)], ['215', '216'])).
% 0.67/0.84  thf('218', plain,
% 0.67/0.84      (![X0 : $i]:
% 0.67/0.84         ((v2_struct_0 @ X0)
% 0.67/0.84          | ~ (l1_struct_0 @ X0)
% 0.67/0.84          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.67/0.84      inference('simplify', [status(thm)], ['217'])).
% 0.67/0.84  thf('219', plain,
% 0.67/0.84      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.84        | ~ (l1_struct_0 @ sk_B)
% 0.67/0.84        | (v2_struct_0 @ sk_B))),
% 0.67/0.84      inference('sup-', [status(thm)], ['214', '218'])).
% 0.67/0.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.67/0.84  thf('220', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.84  thf('221', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.84  thf('222', plain, ((v2_struct_0 @ sk_B)),
% 0.67/0.84      inference('demod', [status(thm)], ['219', '220', '221'])).
% 0.67/0.84  thf('223', plain, ($false), inference('demod', [status(thm)], ['0', '222'])).
% 0.67/0.84  
% 0.67/0.84  % SZS output end Refutation
% 0.67/0.84  
% 0.67/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
