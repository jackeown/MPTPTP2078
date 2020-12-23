%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ravOzwiprL

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:51 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  268 (1668 expanded)
%              Number of leaves         :   50 ( 515 expanded)
%              Depth                    :   25
%              Number of atoms          : 2489 (40740 expanded)
%              Number of equality atoms :  175 (2103 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
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
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

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
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('3',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('24',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','27','30'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

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

thf('49',plain,(
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

thf('50',plain,(
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
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('73',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('76',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','63','64','65','66','73','74','75','87'])).

thf('89',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('91',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','15','44','45','46','89','90'])).

thf('92',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('93',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('95',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('100',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('106',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('112',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('113',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('114',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != X25 )
      | ( v1_partfun1 @ X26 @ X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('117',plain,(
    ! [X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v4_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
      | ( v1_partfun1 @ X26 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','119'])).

thf('121',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','120'])).

thf('122',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('124',plain,(
    v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('128',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('129',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('135',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127','135'])).

thf('137',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('138',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','110','136','137'])).

thf('139',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('140',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('142',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('145',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('146',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('147',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','152'])).

thf('154',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','155'])).

thf('157',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('160',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('161',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','161'])).

thf('163',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','162'])).

thf('164',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','163'])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('167',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('170',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['168','169'])).

thf('171',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['91','170'])).

thf('172',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('173',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('174',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('175',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k8_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('178',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k8_relset_1 @ X22 @ X23 @ X24 @ X23 )
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k8_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['176','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['173','181'])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      = ( k1_relset_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['172','182'])).

thf('184',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('186',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('187',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k9_relat_1 @ X7 @ X8 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X7 ) @ X8 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ X0 )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127','135'])).

thf('194',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('195',plain,
    ( ( k9_relat_1 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','184','185','192','193','194'])).

thf('196',plain,(
    ( k9_relat_1 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['171','195'])).

thf('197',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','196'])).

thf('198',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('199',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('200',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('205',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('206',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2
        = ( k7_relat_1 @ X2 @ X3 ) )
      | ~ ( v4_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('207',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('209',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('211',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('213',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('215',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','198','213','214'])).

thf('216',plain,(
    $false ),
    inference(simplify,[status(thm)],['215'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ravOzwiprL
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 532 iterations in 0.178s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.65  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.65  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.65  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.47/0.65  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.47/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.65  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.65  thf(t37_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.47/0.65         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      (![X4 : $i]:
% 0.47/0.65         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.65          | ~ (v1_relat_1 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.65  thf(d3_struct_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf(t62_tops_2, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_struct_0 @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.47/0.65           ( ![C:$i]:
% 0.47/0.65             ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.65                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.65                 ( m1_subset_1 @
% 0.47/0.65                   C @ 
% 0.47/0.65                   ( k1_zfmisc_1 @
% 0.47/0.65                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.65               ( ( ( ( k2_relset_1 @
% 0.47/0.65                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.47/0.65                     ( k2_struct_0 @ B ) ) & 
% 0.47/0.65                   ( v2_funct_1 @ C ) ) =>
% 0.47/0.65                 ( ( ( k1_relset_1 @
% 0.47/0.65                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.65                       ( k2_tops_2 @
% 0.47/0.65                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.47/0.65                     ( k2_struct_0 @ B ) ) & 
% 0.47/0.65                   ( ( k2_relset_1 @
% 0.47/0.65                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.65                       ( k2_tops_2 @
% 0.47/0.65                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.47/0.65                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( l1_struct_0 @ A ) =>
% 0.47/0.65          ( ![B:$i]:
% 0.47/0.65            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.47/0.65              ( ![C:$i]:
% 0.47/0.65                ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.65                    ( v1_funct_2 @
% 0.47/0.65                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.65                    ( m1_subset_1 @
% 0.47/0.65                      C @ 
% 0.47/0.65                      ( k1_zfmisc_1 @
% 0.47/0.65                        ( k2_zfmisc_1 @
% 0.47/0.65                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.65                  ( ( ( ( k2_relset_1 @
% 0.47/0.65                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.47/0.65                        ( k2_struct_0 @ B ) ) & 
% 0.47/0.65                      ( v2_funct_1 @ C ) ) =>
% 0.47/0.65                    ( ( ( k1_relset_1 @
% 0.47/0.65                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.65                          ( k2_tops_2 @
% 0.47/0.65                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.47/0.65                        ( k2_struct_0 @ B ) ) & 
% 0.47/0.65                      ( ( k2_relset_1 @
% 0.47/0.65                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.65                          ( k2_tops_2 @
% 0.47/0.65                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.47/0.65                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_B))
% 0.47/0.65        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65            != (k2_struct_0 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_B))))),
% 0.47/0.65      inference('split', [status(esa)], ['3'])).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65           != (k2_struct_0 @ sk_B))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['2', '4'])).
% 0.47/0.65  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_B))))),
% 0.47/0.65      inference('demod', [status(thm)], ['5', '6'])).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65           != (k2_struct_0 @ sk_B))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_B))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['1', '7'])).
% 0.47/0.65  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('10', plain,
% 0.47/0.65      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_B))))),
% 0.47/0.65      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.65         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.47/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.65         = (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.65         = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(t132_funct_2, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.65       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.65           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.65           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.65         (((X27) = (k1_xboole_0))
% 0.47/0.65          | ~ (v1_funct_1 @ X28)
% 0.47/0.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 0.47/0.65          | (v1_partfun1 @ X28 @ X29)
% 0.47/0.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 0.47/0.65          | ~ (v1_funct_2 @ X28 @ X29 @ X27)
% 0.47/0.65          | ~ (v1_funct_1 @ X28))),
% 0.47/0.65      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.65         (~ (v1_funct_2 @ X28 @ X29 @ X27)
% 0.47/0.65          | (v1_partfun1 @ X28 @ X29)
% 0.47/0.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 0.47/0.65          | ~ (v1_funct_1 @ X28)
% 0.47/0.65          | ((X27) = (k1_xboole_0)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['17'])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.65        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.65        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['16', '18'])).
% 0.47/0.65  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.47/0.65  thf(d4_partfun1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.65       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i]:
% 0.47/0.65         (~ (v1_partfun1 @ X26 @ X25)
% 0.47/0.65          | ((k1_relat_1 @ X26) = (X25))
% 0.47/0.65          | ~ (v4_relat_1 @ X26 @ X25)
% 0.47/0.65          | ~ (v1_relat_1 @ X26))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(cc1_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( v1_relat_1 @ C ) ))).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.65         ((v1_relat_1 @ X9)
% 0.47/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.65  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(cc2_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.65         ((v4_relat_1 @ X12 @ X13)
% 0.47/0.65          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.65  thf('30', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.65  thf('31', plain,
% 0.47/0.65      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.47/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['24', '27', '30'])).
% 0.47/0.65  thf(fc2_struct_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (![X32 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.47/0.65          | ~ (l1_struct_0 @ X32)
% 0.47/0.65          | (v2_struct_0 @ X32))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.65  thf('33', plain,
% 0.47/0.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.47/0.65        | (v2_struct_0 @ sk_B)
% 0.47/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.65  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('36', plain,
% 0.47/0.65      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.47/0.65      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.47/0.65  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('38', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('clc', [status(thm)], ['36', '37'])).
% 0.47/0.65  thf('39', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('40', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('clc', [status(thm)], ['36', '37'])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['39', '40'])).
% 0.47/0.65  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('43', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('44', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['38', '43'])).
% 0.47/0.65  thf('45', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['38', '43'])).
% 0.47/0.65  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf('47', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf(t3_funct_2, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.65       ( ( v1_funct_1 @ A ) & 
% 0.47/0.65         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.47/0.65         ( m1_subset_1 @
% 0.47/0.65           A @ 
% 0.47/0.65           ( k1_zfmisc_1 @
% 0.47/0.65             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.65  thf('48', plain,
% 0.47/0.65      (![X30 : $i]:
% 0.47/0.65         ((m1_subset_1 @ X30 @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 0.47/0.65          | ~ (v1_funct_1 @ X30)
% 0.47/0.65          | ~ (v1_relat_1 @ X30))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.65  thf(d4_tops_2, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.65       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.47/0.65         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.65         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.47/0.65          | ~ (v2_funct_1 @ X35)
% 0.47/0.65          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.47/0.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.47/0.65          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.47/0.65          | ~ (v1_funct_1 @ X35))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.47/0.65  thf('50', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.65          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.47/0.65              = (k2_funct_1 @ X0))
% 0.47/0.65          | ~ (v2_funct_1 @ X0)
% 0.47/0.65          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.47/0.65              != (k2_relat_1 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.47/0.65            != (k2_relat_1 @ X0))
% 0.47/0.65          | ~ (v2_funct_1 @ X0)
% 0.47/0.65          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.47/0.65              = (k2_funct_1 @ X0))
% 0.47/0.65          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['50'])).
% 0.47/0.65  thf('52', plain,
% 0.47/0.65      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.65        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.65            = (k2_funct_1 @ sk_C))
% 0.47/0.65        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.65        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.65            != (k2_relat_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['47', '51'])).
% 0.47/0.65  thf('53', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('54', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('55', plain,
% 0.47/0.65      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['54', '55'])).
% 0.47/0.65  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('58', plain,
% 0.47/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.65      inference('demod', [status(thm)], ['56', '57'])).
% 0.47/0.65  thf('59', plain,
% 0.47/0.65      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['53', '58'])).
% 0.47/0.65  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('61', plain,
% 0.47/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.47/0.65  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf('63', plain,
% 0.47/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['61', '62'])).
% 0.47/0.65  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('66', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d9_funct_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.65       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.47/0.65  thf('68', plain,
% 0.47/0.65      (![X5 : $i]:
% 0.47/0.65         (~ (v2_funct_1 @ X5)
% 0.47/0.65          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.47/0.65          | ~ (v1_funct_1 @ X5)
% 0.47/0.65          | ~ (v1_relat_1 @ X5))),
% 0.47/0.65      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.47/0.65  thf('69', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.65  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('71', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.47/0.65      inference('demod', [status(thm)], ['69', '70'])).
% 0.47/0.65  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('73', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.65  thf('74', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('75', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('76', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('77', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('78', plain,
% 0.47/0.65      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.65         = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('79', plain,
% 0.47/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.65          = (k2_struct_0 @ sk_B))
% 0.47/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['77', '78'])).
% 0.47/0.65  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('81', plain,
% 0.47/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.65         = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('demod', [status(thm)], ['79', '80'])).
% 0.47/0.65  thf('82', plain,
% 0.47/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.65          = (k2_struct_0 @ sk_B))
% 0.47/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['76', '81'])).
% 0.47/0.65  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('84', plain,
% 0.47/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.65         = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.65  thf('85', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf('87', plain,
% 0.47/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.65         = (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.47/0.65  thf('88', plain,
% 0.47/0.65      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.65          = (k4_relat_1 @ sk_C))
% 0.47/0.65        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['52', '63', '64', '65', '66', '73', '74', '75', '87'])).
% 0.47/0.65  thf('89', plain,
% 0.47/0.65      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.65         = (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('simplify', [status(thm)], ['88'])).
% 0.47/0.65  thf('90', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf('91', plain,
% 0.47/0.65      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_B))))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['10', '15', '44', '45', '46', '89', '90'])).
% 0.47/0.65  thf('92', plain,
% 0.47/0.65      (![X4 : $i]:
% 0.47/0.65         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.65          | ~ (v1_relat_1 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.65  thf('93', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.65  thf(dt_k2_funct_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.65       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.65         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.47/0.65  thf('94', plain,
% 0.47/0.65      (![X6 : $i]:
% 0.47/0.65         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.47/0.65          | ~ (v1_funct_1 @ X6)
% 0.47/0.65          | ~ (v1_relat_1 @ X6))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.65  thf('95', plain,
% 0.47/0.65      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['93', '94'])).
% 0.47/0.65  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('98', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.47/0.65  thf('99', plain,
% 0.47/0.65      (![X4 : $i]:
% 0.47/0.65         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.65          | ~ (v1_relat_1 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.65  thf('100', plain,
% 0.47/0.65      (![X30 : $i]:
% 0.47/0.65         ((m1_subset_1 @ X30 @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 0.47/0.65          | ~ (v1_funct_1 @ X30)
% 0.47/0.65          | ~ (v1_relat_1 @ X30))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.65  thf('101', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (k4_relat_1 @ X0) @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0))))
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['99', '100'])).
% 0.47/0.65  thf('102', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.47/0.65             (k1_relat_1 @ sk_C)))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['98', '101'])).
% 0.47/0.65  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('104', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.47/0.65        | (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.47/0.65             (k1_relat_1 @ sk_C)))))),
% 0.47/0.65      inference('demod', [status(thm)], ['102', '103'])).
% 0.47/0.65  thf('105', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.65  thf('106', plain,
% 0.47/0.65      (![X6 : $i]:
% 0.47/0.65         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 0.47/0.65          | ~ (v1_funct_1 @ X6)
% 0.47/0.65          | ~ (v1_relat_1 @ X6))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.65  thf('107', plain,
% 0.47/0.65      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['105', '106'])).
% 0.47/0.65  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('110', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.47/0.65  thf('111', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.47/0.65  thf('112', plain,
% 0.47/0.65      (![X4 : $i]:
% 0.47/0.65         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.65          | ~ (v1_relat_1 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.65  thf('113', plain,
% 0.47/0.65      (![X30 : $i]:
% 0.47/0.65         ((m1_subset_1 @ X30 @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 0.47/0.65          | ~ (v1_funct_1 @ X30)
% 0.47/0.65          | ~ (v1_relat_1 @ X30))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.65  thf('114', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.65         ((v4_relat_1 @ X12 @ X13)
% 0.47/0.65          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.65  thf('115', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['113', '114'])).
% 0.47/0.65  thf('116', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i]:
% 0.47/0.65         (((k1_relat_1 @ X26) != (X25))
% 0.47/0.65          | (v1_partfun1 @ X26 @ X25)
% 0.47/0.65          | ~ (v4_relat_1 @ X26 @ X25)
% 0.47/0.65          | ~ (v1_relat_1 @ X26))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.65  thf('117', plain,
% 0.47/0.65      (![X26 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X26)
% 0.47/0.65          | ~ (v4_relat_1 @ X26 @ (k1_relat_1 @ X26))
% 0.47/0.65          | (v1_partfun1 @ X26 @ (k1_relat_1 @ X26)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['116'])).
% 0.47/0.65  thf('118', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['115', '117'])).
% 0.47/0.65  thf('119', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['118'])).
% 0.47/0.65  thf('120', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_partfun1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['112', '119'])).
% 0.47/0.65  thf('121', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | (v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['111', '120'])).
% 0.47/0.65  thf('122', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.47/0.65  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('124', plain,
% 0.47/0.65      ((v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.47/0.65  thf('125', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i]:
% 0.47/0.65         (~ (v1_partfun1 @ X26 @ X25)
% 0.47/0.65          | ((k1_relat_1 @ X26) = (X25))
% 0.47/0.65          | ~ (v4_relat_1 @ X26 @ X25)
% 0.47/0.65          | ~ (v1_relat_1 @ X26))),
% 0.47/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.65  thf('126', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.47/0.65        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['124', '125'])).
% 0.47/0.65  thf('127', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.47/0.65  thf('128', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.47/0.65  thf('129', plain,
% 0.47/0.65      (![X4 : $i]:
% 0.47/0.65         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.65          | ~ (v1_relat_1 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.65  thf('130', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['113', '114'])).
% 0.47/0.65  thf('131', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v4_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['129', '130'])).
% 0.47/0.65  thf('132', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | (v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['128', '131'])).
% 0.47/0.65  thf('133', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.47/0.65  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('135', plain, ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.47/0.65  thf('136', plain,
% 0.47/0.65      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['126', '127', '135'])).
% 0.47/0.65  thf('137', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('138', plain,
% 0.47/0.65      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['104', '110', '136', '137'])).
% 0.47/0.65  thf('139', plain,
% 0.47/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.65         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.47/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.65  thf('140', plain,
% 0.47/0.65      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['138', '139'])).
% 0.47/0.65  thf('141', plain,
% 0.47/0.65      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.65         = (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('simplify', [status(thm)], ['88'])).
% 0.47/0.65  thf('142', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('143', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('144', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('145', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('146', plain,
% 0.47/0.65      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('split', [status(esa)], ['3'])).
% 0.47/0.65  thf('147', plain,
% 0.47/0.65      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65           != (k2_struct_0 @ sk_A))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['145', '146'])).
% 0.47/0.65  thf('148', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('149', plain,
% 0.47/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['147', '148'])).
% 0.47/0.65  thf('150', plain,
% 0.47/0.65      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65           != (k2_struct_0 @ sk_A))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['144', '149'])).
% 0.47/0.65  thf('151', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('152', plain,
% 0.47/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['150', '151'])).
% 0.47/0.65  thf('153', plain,
% 0.47/0.65      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65           != (k2_struct_0 @ sk_A))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['143', '152'])).
% 0.47/0.65  thf('154', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('155', plain,
% 0.47/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['153', '154'])).
% 0.47/0.65  thf('156', plain,
% 0.47/0.65      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65           != (k2_struct_0 @ sk_A))
% 0.47/0.65         | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['142', '155'])).
% 0.47/0.65  thf('157', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('158', plain,
% 0.47/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['156', '157'])).
% 0.47/0.65  thf('159', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf('160', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf('161', plain,
% 0.47/0.65      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.47/0.65          != (k2_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.47/0.65  thf('162', plain,
% 0.47/0.65      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65          (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['141', '161'])).
% 0.47/0.65  thf('163', plain,
% 0.47/0.65      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['140', '162'])).
% 0.47/0.65  thf('164', plain,
% 0.47/0.65      (((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)) | ~ (v1_relat_1 @ sk_C)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['92', '163'])).
% 0.47/0.65  thf('165', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('167', plain,
% 0.47/0.65      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65                = (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['164', '165', '166'])).
% 0.47/0.65  thf('168', plain,
% 0.47/0.65      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          = (k2_struct_0 @ sk_A)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['167'])).
% 0.47/0.65  thf('169', plain,
% 0.47/0.65      (~
% 0.47/0.65       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          = (k2_struct_0 @ sk_B))) | 
% 0.47/0.65       ~
% 0.47/0.65       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          = (k2_struct_0 @ sk_A)))),
% 0.47/0.65      inference('split', [status(esa)], ['3'])).
% 0.47/0.65  thf('170', plain,
% 0.47/0.65      (~
% 0.47/0.65       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.65          = (k2_struct_0 @ sk_B)))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)], ['168', '169'])).
% 0.47/0.65  thf('171', plain,
% 0.47/0.65      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65         (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['91', '170'])).
% 0.47/0.65  thf('172', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.47/0.65  thf('173', plain,
% 0.47/0.65      (![X4 : $i]:
% 0.47/0.65         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.47/0.65          | ~ (v1_relat_1 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.47/0.65  thf('174', plain,
% 0.47/0.65      (![X30 : $i]:
% 0.47/0.65         ((m1_subset_1 @ X30 @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 0.47/0.65          | ~ (v1_funct_1 @ X30)
% 0.47/0.65          | ~ (v1_relat_1 @ X30))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.65  thf(redefinition_k8_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.47/0.65  thf('175', plain,
% 0.47/0.65      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.47/0.65          | ((k8_relset_1 @ X19 @ X20 @ X18 @ X21) = (k10_relat_1 @ X18 @ X21)))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.47/0.65  thf('176', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ((k8_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.47/0.65              = (k10_relat_1 @ X0 @ X1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['174', '175'])).
% 0.47/0.65  thf('177', plain,
% 0.47/0.65      (![X30 : $i]:
% 0.47/0.65         ((m1_subset_1 @ X30 @ 
% 0.47/0.65           (k1_zfmisc_1 @ 
% 0.47/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30))))
% 0.47/0.65          | ~ (v1_funct_1 @ X30)
% 0.47/0.65          | ~ (v1_relat_1 @ X30))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.47/0.65  thf(t38_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.47/0.65         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.65  thf('178', plain,
% 0.47/0.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.65         (((k8_relset_1 @ X22 @ X23 @ X24 @ X23)
% 0.47/0.65            = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.47/0.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.47/0.65      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.47/0.65  thf('179', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ((k8_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ 
% 0.47/0.65              (k2_relat_1 @ X0))
% 0.47/0.65              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['177', '178'])).
% 0.47/0.65  thf('180', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.47/0.65            = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['176', '179'])).
% 0.47/0.65  thf('181', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.47/0.65              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['180'])).
% 0.47/0.65  thf('182', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k10_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.47/0.65            = (k1_relset_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ 
% 0.47/0.65               (k1_relat_1 @ X0) @ (k4_relat_1 @ X0)))
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['173', '181'])).
% 0.47/0.65  thf('183', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ((k10_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 0.47/0.65            (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.47/0.65            = (k1_relset_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.47/0.65               (k1_relat_1 @ sk_C) @ (k4_relat_1 @ sk_C))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['172', '182'])).
% 0.47/0.65  thf('184', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.47/0.65  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('186', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.65  thf(t154_funct_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.65       ( ( v2_funct_1 @ B ) =>
% 0.47/0.65         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.47/0.65  thf('187', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i]:
% 0.47/0.65         (~ (v2_funct_1 @ X7)
% 0.47/0.65          | ((k9_relat_1 @ X7 @ X8) = (k10_relat_1 @ (k2_funct_1 @ X7) @ X8))
% 0.47/0.65          | ~ (v1_funct_1 @ X7)
% 0.47/0.65          | ~ (v1_relat_1 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.47/0.65  thf('188', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k9_relat_1 @ sk_C @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ sk_C)
% 0.47/0.65          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.65          | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['186', '187'])).
% 0.47/0.65  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('192', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k9_relat_1 @ sk_C @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 0.47/0.65  thf('193', plain,
% 0.47/0.65      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['126', '127', '135'])).
% 0.47/0.65  thf('194', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('195', plain,
% 0.47/0.65      (((k9_relat_1 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.47/0.65         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.65            (k4_relat_1 @ sk_C)))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['183', '184', '185', '192', '193', '194'])).
% 0.47/0.65  thf('196', plain,
% 0.47/0.65      (((k9_relat_1 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.47/0.65         != (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['171', '195'])).
% 0.47/0.65  thf('197', plain,
% 0.47/0.65      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.65      inference('sup-', [status(thm)], ['0', '196'])).
% 0.47/0.65  thf('198', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '42'])).
% 0.47/0.65  thf('199', plain,
% 0.47/0.65      (![X31 : $i]:
% 0.47/0.65         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.65  thf('200', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('201', plain,
% 0.47/0.65      (((m1_subset_1 @ sk_C @ 
% 0.47/0.65         (k1_zfmisc_1 @ 
% 0.47/0.65          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['199', '200'])).
% 0.47/0.65  thf('202', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('203', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_C @ 
% 0.47/0.65        (k1_zfmisc_1 @ 
% 0.47/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.65      inference('demod', [status(thm)], ['201', '202'])).
% 0.47/0.65  thf('204', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.65         ((v4_relat_1 @ X12 @ X13)
% 0.47/0.65          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.65  thf('205', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['203', '204'])).
% 0.47/0.65  thf(t209_relat_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.65       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.47/0.65  thf('206', plain,
% 0.47/0.65      (![X2 : $i, X3 : $i]:
% 0.47/0.65         (((X2) = (k7_relat_1 @ X2 @ X3))
% 0.47/0.65          | ~ (v4_relat_1 @ X2 @ X3)
% 0.47/0.65          | ~ (v1_relat_1 @ X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.47/0.65  thf('207', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.65        | ((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['205', '206'])).
% 0.47/0.65  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('209', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['207', '208'])).
% 0.47/0.65  thf(t148_relat_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ B ) =>
% 0.47/0.65       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.47/0.65  thf('210', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (k9_relat_1 @ X0 @ X1))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.65  thf('211', plain,
% 0.47/0.65      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.65      inference('sup+', [status(thm)], ['209', '210'])).
% 0.47/0.65  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('213', plain,
% 0.47/0.65      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['211', '212'])).
% 0.47/0.65  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('215', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.47/0.65      inference('demod', [status(thm)], ['197', '198', '213', '214'])).
% 0.47/0.65  thf('216', plain, ($false), inference('simplify', [status(thm)], ['215'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
