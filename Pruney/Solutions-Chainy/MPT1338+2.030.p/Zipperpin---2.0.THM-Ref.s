%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cUDxHJfhdj

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:52 EST 2020

% Result     : Theorem 2.55s
% Output     : Refutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  235 (2726 expanded)
%              Number of leaves         :   45 ( 816 expanded)
%              Depth                    :   24
%              Number of atoms          : 2274 (71519 expanded)
%              Number of equality atoms :  169 (3747 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf('1',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X23 @ X21 )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22','25'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('27',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('35',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

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

thf('39',plain,(
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

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ X2 )
        = ( k4_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('51',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('55',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','44','51','52','55'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('63',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','10','33','34','61','62'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('65',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

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

thf('74',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('87',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('88',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('94',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('96',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','85','86','96','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('101',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('103',plain,(
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

thf('104',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('107',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('110',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108','109'])).

thf('111',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('117',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('127',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('130',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('134',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('138',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('139',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','136','137','138'])).

thf('140',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','139'])).

thf('141',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','140'])).

thf('142',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('144',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('147',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['145','146'])).

thf('148',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['63','147'])).

thf('149',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('150',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('151',plain,
    ( ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('153',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k10_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','154'])).

thf('156',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('157',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('158',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('164',plain,
    ( ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('166',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('167',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('168',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('170',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != X19 )
      | ( v1_partfun1 @ X20 @ X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('171',plain,(
    ! [X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v4_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
      | ( v1_partfun1 @ X20 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['169','171'])).

thf('173',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['168','172'])).

thf('174',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('176',plain,(
    v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['165','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('179',plain,(
    v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('183',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('184',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','184'])).

thf('186',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','185'])).

thf('187',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','186'])).

thf('188',plain,(
    $false ),
    inference(simplify,[status(thm)],['187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cUDxHJfhdj
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.55/2.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.55/2.80  % Solved by: fo/fo7.sh
% 2.55/2.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.55/2.80  % done 459 iterations in 2.337s
% 2.55/2.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.55/2.80  % SZS output start Refutation
% 2.55/2.80  thf(sk_B_type, type, sk_B: $i).
% 2.55/2.80  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.55/2.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.55/2.80  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.55/2.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.55/2.80  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.55/2.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.55/2.80  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.55/2.80  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 2.55/2.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.55/2.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.55/2.80  thf(sk_A_type, type, sk_A: $i).
% 2.55/2.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.55/2.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.55/2.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.55/2.80  thf(sk_C_type, type, sk_C: $i).
% 2.55/2.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.55/2.80  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.55/2.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.55/2.80  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 2.55/2.80  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.55/2.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.55/2.80  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.55/2.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.55/2.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.55/2.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.55/2.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.55/2.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.55/2.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.55/2.80  thf(d3_struct_0, axiom,
% 2.55/2.80    (![A:$i]:
% 2.55/2.80     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.55/2.80  thf('0', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf(t62_tops_2, conjecture,
% 2.55/2.80    (![A:$i]:
% 2.55/2.80     ( ( l1_struct_0 @ A ) =>
% 2.55/2.80       ( ![B:$i]:
% 2.55/2.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.55/2.80           ( ![C:$i]:
% 2.55/2.80             ( ( ( v1_funct_1 @ C ) & 
% 2.55/2.80                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.55/2.80                 ( m1_subset_1 @
% 2.55/2.80                   C @ 
% 2.55/2.80                   ( k1_zfmisc_1 @
% 2.55/2.80                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.55/2.80               ( ( ( ( k2_relset_1 @
% 2.55/2.80                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.55/2.80                     ( k2_struct_0 @ B ) ) & 
% 2.55/2.80                   ( v2_funct_1 @ C ) ) =>
% 2.55/2.80                 ( ( ( k1_relset_1 @
% 2.55/2.80                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.55/2.80                       ( k2_tops_2 @
% 2.55/2.80                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.55/2.80                     ( k2_struct_0 @ B ) ) & 
% 2.55/2.80                   ( ( k2_relset_1 @
% 2.55/2.80                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.55/2.80                       ( k2_tops_2 @
% 2.55/2.80                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.55/2.80                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 2.55/2.80  thf(zf_stmt_0, negated_conjecture,
% 2.55/2.80    (~( ![A:$i]:
% 2.55/2.80        ( ( l1_struct_0 @ A ) =>
% 2.55/2.80          ( ![B:$i]:
% 2.55/2.80            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.55/2.80              ( ![C:$i]:
% 2.55/2.80                ( ( ( v1_funct_1 @ C ) & 
% 2.55/2.80                    ( v1_funct_2 @
% 2.55/2.80                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.55/2.80                    ( m1_subset_1 @
% 2.55/2.80                      C @ 
% 2.55/2.80                      ( k1_zfmisc_1 @
% 2.55/2.80                        ( k2_zfmisc_1 @
% 2.55/2.80                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.55/2.80                  ( ( ( ( k2_relset_1 @
% 2.55/2.80                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.55/2.80                        ( k2_struct_0 @ B ) ) & 
% 2.55/2.80                      ( v2_funct_1 @ C ) ) =>
% 2.55/2.80                    ( ( ( k1_relset_1 @
% 2.55/2.80                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.55/2.80                          ( k2_tops_2 @
% 2.55/2.80                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.55/2.80                        ( k2_struct_0 @ B ) ) & 
% 2.55/2.80                      ( ( k2_relset_1 @
% 2.55/2.80                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.55/2.80                          ( k2_tops_2 @
% 2.55/2.80                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.55/2.80                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 2.55/2.80    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 2.55/2.80  thf('1', plain,
% 2.55/2.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          != (k2_struct_0 @ sk_B))
% 2.55/2.80        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80            != (k2_struct_0 @ sk_A)))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('2', plain,
% 2.55/2.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          != (k2_struct_0 @ sk_B)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_B))))),
% 2.55/2.80      inference('split', [status(esa)], ['1'])).
% 2.55/2.80  thf('3', plain,
% 2.55/2.80      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80           != (k2_struct_0 @ sk_B))
% 2.55/2.80         | ~ (l1_struct_0 @ sk_B)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_B))))),
% 2.55/2.80      inference('sup-', [status(thm)], ['0', '2'])).
% 2.55/2.80  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('5', plain,
% 2.55/2.80      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          != (k2_struct_0 @ sk_B)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_B))))),
% 2.55/2.80      inference('demod', [status(thm)], ['3', '4'])).
% 2.55/2.80  thf('6', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf(redefinition_k2_relset_1, axiom,
% 2.55/2.80    (![A:$i,B:$i,C:$i]:
% 2.55/2.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.55/2.80       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.55/2.80  thf('7', plain,
% 2.55/2.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.55/2.80         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 2.55/2.80          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.55/2.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.55/2.80  thf('8', plain,
% 2.55/2.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80         = (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['6', '7'])).
% 2.55/2.80  thf('9', plain,
% 2.55/2.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80         = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('10', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['8', '9'])).
% 2.55/2.80  thf('11', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf(t132_funct_2, axiom,
% 2.55/2.80    (![A:$i,B:$i,C:$i]:
% 2.55/2.80     ( ( ( v1_funct_1 @ C ) & 
% 2.55/2.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.55/2.80       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.55/2.80           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.55/2.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.55/2.80           ( v1_partfun1 @ C @ A ) ) ) ))).
% 2.55/2.80  thf('12', plain,
% 2.55/2.80      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.55/2.80         (((X21) = (k1_xboole_0))
% 2.55/2.80          | ~ (v1_funct_1 @ X22)
% 2.55/2.80          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 2.55/2.80          | (v1_partfun1 @ X22 @ X23)
% 2.55/2.80          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 2.55/2.80          | ~ (v1_funct_2 @ X22 @ X23 @ X21)
% 2.55/2.80          | ~ (v1_funct_1 @ X22))),
% 2.55/2.80      inference('cnf', [status(esa)], [t132_funct_2])).
% 2.55/2.80  thf('13', plain,
% 2.55/2.80      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.55/2.80         (~ (v1_funct_2 @ X22 @ X23 @ X21)
% 2.55/2.80          | (v1_partfun1 @ X22 @ X23)
% 2.55/2.80          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 2.55/2.80          | ~ (v1_funct_1 @ X22)
% 2.55/2.80          | ((X21) = (k1_xboole_0)))),
% 2.55/2.80      inference('simplify', [status(thm)], ['12'])).
% 2.55/2.80  thf('14', plain,
% 2.55/2.80      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.55/2.80        | ~ (v1_funct_1 @ sk_C)
% 2.55/2.80        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.55/2.80        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 2.55/2.80      inference('sup-', [status(thm)], ['11', '13'])).
% 2.55/2.80  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('16', plain,
% 2.55/2.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('17', plain,
% 2.55/2.80      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.55/2.80        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 2.55/2.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 2.55/2.80  thf(d4_partfun1, axiom,
% 2.55/2.80    (![A:$i,B:$i]:
% 2.55/2.80     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.55/2.80       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 2.55/2.80  thf('18', plain,
% 2.55/2.80      (![X19 : $i, X20 : $i]:
% 2.55/2.80         (~ (v1_partfun1 @ X20 @ X19)
% 2.55/2.80          | ((k1_relat_1 @ X20) = (X19))
% 2.55/2.80          | ~ (v4_relat_1 @ X20 @ X19)
% 2.55/2.80          | ~ (v1_relat_1 @ X20))),
% 2.55/2.80      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.55/2.80  thf('19', plain,
% 2.55/2.80      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.55/2.80        | ~ (v1_relat_1 @ sk_C)
% 2.55/2.80        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.55/2.80        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.55/2.80      inference('sup-', [status(thm)], ['17', '18'])).
% 2.55/2.80  thf('20', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf(cc1_relset_1, axiom,
% 2.55/2.80    (![A:$i,B:$i,C:$i]:
% 2.55/2.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.55/2.80       ( v1_relat_1 @ C ) ))).
% 2.55/2.80  thf('21', plain,
% 2.55/2.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.55/2.80         ((v1_relat_1 @ X3)
% 2.55/2.80          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.55/2.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.55/2.80  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 2.55/2.80      inference('sup-', [status(thm)], ['20', '21'])).
% 2.55/2.80  thf('23', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf(cc2_relset_1, axiom,
% 2.55/2.80    (![A:$i,B:$i,C:$i]:
% 2.55/2.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.55/2.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.55/2.80  thf('24', plain,
% 2.55/2.80      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.55/2.80         ((v4_relat_1 @ X6 @ X7)
% 2.55/2.80          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.55/2.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.55/2.80  thf('25', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('sup-', [status(thm)], ['23', '24'])).
% 2.55/2.80  thf('26', plain,
% 2.55/2.80      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.55/2.80        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.55/2.80      inference('demod', [status(thm)], ['19', '22', '25'])).
% 2.55/2.80  thf(fc2_struct_0, axiom,
% 2.55/2.80    (![A:$i]:
% 2.55/2.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.55/2.80       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.55/2.80  thf('27', plain,
% 2.55/2.80      (![X28 : $i]:
% 2.55/2.80         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 2.55/2.80          | ~ (l1_struct_0 @ X28)
% 2.55/2.80          | (v2_struct_0 @ X28))),
% 2.55/2.80      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.55/2.80  thf('28', plain,
% 2.55/2.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.55/2.80        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 2.55/2.80        | (v2_struct_0 @ sk_B)
% 2.55/2.80        | ~ (l1_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup-', [status(thm)], ['26', '27'])).
% 2.55/2.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.55/2.80  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.55/2.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.55/2.80  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('31', plain,
% 2.55/2.80      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 2.55/2.80      inference('demod', [status(thm)], ['28', '29', '30'])).
% 2.55/2.80  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('33', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('clc', [status(thm)], ['31', '32'])).
% 2.55/2.80  thf('34', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('clc', [status(thm)], ['31', '32'])).
% 2.55/2.80  thf('35', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf('36', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('37', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('clc', [status(thm)], ['31', '32'])).
% 2.55/2.80  thf('38', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 2.55/2.80      inference('demod', [status(thm)], ['36', '37'])).
% 2.55/2.80  thf(d4_tops_2, axiom,
% 2.55/2.80    (![A:$i,B:$i,C:$i]:
% 2.55/2.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.55/2.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.55/2.80       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.55/2.80         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 2.55/2.80  thf('39', plain,
% 2.55/2.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.55/2.80         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 2.55/2.80          | ~ (v2_funct_1 @ X31)
% 2.55/2.80          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 2.55/2.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 2.55/2.80          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 2.55/2.80          | ~ (v1_funct_1 @ X31))),
% 2.55/2.80      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.55/2.80  thf('40', plain,
% 2.55/2.80      ((~ (v1_funct_1 @ sk_C)
% 2.55/2.80        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 2.55/2.80        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80            = (k2_funct_1 @ sk_C))
% 2.55/2.80        | ~ (v2_funct_1 @ sk_C)
% 2.55/2.80        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80            != (u1_struct_0 @ sk_B)))),
% 2.55/2.80      inference('sup-', [status(thm)], ['38', '39'])).
% 2.55/2.80  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('42', plain,
% 2.55/2.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('43', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('clc', [status(thm)], ['31', '32'])).
% 2.55/2.80  thf('44', plain,
% 2.55/2.80      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 2.55/2.80      inference('demod', [status(thm)], ['42', '43'])).
% 2.55/2.80  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf(d9_funct_1, axiom,
% 2.55/2.80    (![A:$i]:
% 2.55/2.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.55/2.80       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.55/2.80  thf('46', plain,
% 2.55/2.80      (![X2 : $i]:
% 2.55/2.80         (~ (v2_funct_1 @ X2)
% 2.55/2.80          | ((k2_funct_1 @ X2) = (k4_relat_1 @ X2))
% 2.55/2.80          | ~ (v1_funct_1 @ X2)
% 2.55/2.80          | ~ (v1_relat_1 @ X2))),
% 2.55/2.80      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.55/2.80  thf('47', plain,
% 2.55/2.80      ((~ (v1_relat_1 @ sk_C)
% 2.55/2.80        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 2.55/2.80        | ~ (v2_funct_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['45', '46'])).
% 2.55/2.80  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('49', plain,
% 2.55/2.80      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 2.55/2.80      inference('demod', [status(thm)], ['47', '48'])).
% 2.55/2.80  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 2.55/2.80      inference('sup-', [status(thm)], ['20', '21'])).
% 2.55/2.80  thf('51', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['49', '50'])).
% 2.55/2.80  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('53', plain,
% 2.55/2.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80         = (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['6', '7'])).
% 2.55/2.80  thf('54', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('clc', [status(thm)], ['31', '32'])).
% 2.55/2.80  thf('55', plain,
% 2.55/2.80      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80         = (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['53', '54'])).
% 2.55/2.80  thf('56', plain,
% 2.55/2.80      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80          = (k4_relat_1 @ sk_C))
% 2.55/2.80        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 2.55/2.80      inference('demod', [status(thm)], ['40', '41', '44', '51', '52', '55'])).
% 2.55/2.80  thf('57', plain,
% 2.55/2.80      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 2.55/2.80        | ~ (l1_struct_0 @ sk_B)
% 2.55/2.80        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80            = (k4_relat_1 @ sk_C)))),
% 2.55/2.80      inference('sup-', [status(thm)], ['35', '56'])).
% 2.55/2.80  thf('58', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['8', '9'])).
% 2.55/2.80  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('60', plain,
% 2.55/2.80      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 2.55/2.80        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80            = (k4_relat_1 @ sk_C)))),
% 2.55/2.80      inference('demod', [status(thm)], ['57', '58', '59'])).
% 2.55/2.80  thf('61', plain,
% 2.55/2.80      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80         = (k4_relat_1 @ sk_C))),
% 2.55/2.80      inference('simplify', [status(thm)], ['60'])).
% 2.55/2.80  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['8', '9'])).
% 2.55/2.80  thf('63', plain,
% 2.55/2.80      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_B))))),
% 2.55/2.80      inference('demod', [status(thm)], ['5', '10', '33', '34', '61', '62'])).
% 2.55/2.80  thf(t37_relat_1, axiom,
% 2.55/2.80    (![A:$i]:
% 2.55/2.80     ( ( v1_relat_1 @ A ) =>
% 2.55/2.80       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 2.55/2.80         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 2.55/2.80  thf('64', plain,
% 2.55/2.80      (![X1 : $i]:
% 2.55/2.80         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 2.55/2.80          | ~ (v1_relat_1 @ X1))),
% 2.55/2.80      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.55/2.80  thf('65', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf('66', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('67', plain,
% 2.55/2.80      (((m1_subset_1 @ sk_C @ 
% 2.55/2.80         (k1_zfmisc_1 @ 
% 2.55/2.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 2.55/2.80        | ~ (l1_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['65', '66'])).
% 2.55/2.80  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('69', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.55/2.80      inference('demod', [status(thm)], ['67', '68'])).
% 2.55/2.80  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['8', '9'])).
% 2.55/2.80  thf('71', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.55/2.80      inference('demod', [status(thm)], ['69', '70'])).
% 2.55/2.80  thf('72', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('clc', [status(thm)], ['31', '32'])).
% 2.55/2.80  thf('73', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.55/2.80      inference('demod', [status(thm)], ['71', '72'])).
% 2.55/2.80  thf(t31_funct_2, axiom,
% 2.55/2.80    (![A:$i,B:$i,C:$i]:
% 2.55/2.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.55/2.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.55/2.80       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.55/2.80         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.55/2.80           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.55/2.80           ( m1_subset_1 @
% 2.55/2.80             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.55/2.80  thf('74', plain,
% 2.55/2.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.55/2.80         (~ (v2_funct_1 @ X24)
% 2.55/2.80          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 2.55/2.80          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 2.55/2.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.55/2.80          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 2.55/2.80          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 2.55/2.80          | ~ (v1_funct_1 @ X24))),
% 2.55/2.80      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.55/2.80  thf('75', plain,
% 2.55/2.80      ((~ (v1_funct_1 @ sk_C)
% 2.55/2.80        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.55/2.80        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.55/2.80           (k1_zfmisc_1 @ 
% 2.55/2.80            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 2.55/2.80        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.55/2.80            != (k2_relat_1 @ sk_C))
% 2.55/2.80        | ~ (v2_funct_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['73', '74'])).
% 2.55/2.80  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('77', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf('78', plain,
% 2.55/2.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('79', plain,
% 2.55/2.80      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.55/2.80        | ~ (l1_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['77', '78'])).
% 2.55/2.80  thf('80', plain, ((l1_struct_0 @ sk_B)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('81', plain,
% 2.55/2.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('demod', [status(thm)], ['79', '80'])).
% 2.55/2.80  thf('82', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['8', '9'])).
% 2.55/2.80  thf('83', plain,
% 2.55/2.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['81', '82'])).
% 2.55/2.80  thf('84', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('clc', [status(thm)], ['31', '32'])).
% 2.55/2.80  thf('85', plain,
% 2.55/2.80      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['83', '84'])).
% 2.55/2.80  thf('86', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['49', '50'])).
% 2.55/2.80  thf('87', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf('88', plain,
% 2.55/2.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80         = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('89', plain,
% 2.55/2.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80          = (k2_struct_0 @ sk_B))
% 2.55/2.80        | ~ (l1_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['87', '88'])).
% 2.55/2.80  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('91', plain,
% 2.55/2.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.55/2.80         = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('demod', [status(thm)], ['89', '90'])).
% 2.55/2.80  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['8', '9'])).
% 2.55/2.80  thf('93', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['8', '9'])).
% 2.55/2.80  thf('94', plain,
% 2.55/2.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.55/2.80         = (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['91', '92', '93'])).
% 2.55/2.80  thf('95', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('clc', [status(thm)], ['31', '32'])).
% 2.55/2.80  thf('96', plain,
% 2.55/2.80      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.55/2.80         = (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['94', '95'])).
% 2.55/2.80  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('98', plain,
% 2.55/2.80      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 2.55/2.80         (k1_zfmisc_1 @ 
% 2.55/2.80          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 2.55/2.80        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.55/2.80      inference('demod', [status(thm)], ['75', '76', '85', '86', '96', '97'])).
% 2.55/2.80  thf('99', plain,
% 2.55/2.80      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.55/2.80      inference('simplify', [status(thm)], ['98'])).
% 2.55/2.80  thf('100', plain,
% 2.55/2.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.55/2.80         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 2.55/2.80          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.55/2.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.55/2.80  thf('101', plain,
% 2.55/2.80      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.55/2.80      inference('sup-', [status(thm)], ['99', '100'])).
% 2.55/2.80  thf('102', plain,
% 2.55/2.80      ((m1_subset_1 @ sk_C @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.55/2.80      inference('demod', [status(thm)], ['71', '72'])).
% 2.55/2.80  thf('103', plain,
% 2.55/2.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.55/2.80         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 2.55/2.80          | ~ (v2_funct_1 @ X31)
% 2.55/2.80          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 2.55/2.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 2.55/2.80          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 2.55/2.80          | ~ (v1_funct_1 @ X31))),
% 2.55/2.80      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.55/2.80  thf('104', plain,
% 2.55/2.80      ((~ (v1_funct_1 @ sk_C)
% 2.55/2.80        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.55/2.80        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.55/2.80            = (k2_funct_1 @ sk_C))
% 2.55/2.80        | ~ (v2_funct_1 @ sk_C)
% 2.55/2.80        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.55/2.80            != (k2_relat_1 @ sk_C)))),
% 2.55/2.80      inference('sup-', [status(thm)], ['102', '103'])).
% 2.55/2.80  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('106', plain,
% 2.55/2.80      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['83', '84'])).
% 2.55/2.80  thf('107', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['49', '50'])).
% 2.55/2.80  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('109', plain,
% 2.55/2.80      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.55/2.80         = (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['94', '95'])).
% 2.55/2.80  thf('110', plain,
% 2.55/2.80      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.55/2.80          = (k4_relat_1 @ sk_C))
% 2.55/2.80        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.55/2.80      inference('demod', [status(thm)],
% 2.55/2.80                ['104', '105', '106', '107', '108', '109'])).
% 2.55/2.80  thf('111', plain,
% 2.55/2.80      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.55/2.80         = (k4_relat_1 @ sk_C))),
% 2.55/2.80      inference('simplify', [status(thm)], ['110'])).
% 2.55/2.80  thf('112', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf('113', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf('114', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf('115', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf('116', plain,
% 2.55/2.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          != (k2_struct_0 @ sk_A)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('split', [status(esa)], ['1'])).
% 2.55/2.80  thf('117', plain,
% 2.55/2.80      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80           != (k2_struct_0 @ sk_A))
% 2.55/2.80         | ~ (l1_struct_0 @ sk_B)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('sup-', [status(thm)], ['115', '116'])).
% 2.55/2.80  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('119', plain,
% 2.55/2.80      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          != (k2_struct_0 @ sk_A)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('demod', [status(thm)], ['117', '118'])).
% 2.55/2.80  thf('120', plain,
% 2.55/2.80      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.55/2.80           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80           != (k2_struct_0 @ sk_A))
% 2.55/2.80         | ~ (l1_struct_0 @ sk_A)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('sup-', [status(thm)], ['114', '119'])).
% 2.55/2.80  thf('121', plain, ((l1_struct_0 @ sk_A)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('122', plain,
% 2.55/2.80      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          != (k2_struct_0 @ sk_A)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('demod', [status(thm)], ['120', '121'])).
% 2.55/2.80  thf('123', plain,
% 2.55/2.80      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.55/2.80           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80           != (k2_struct_0 @ sk_A))
% 2.55/2.80         | ~ (l1_struct_0 @ sk_A)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('sup-', [status(thm)], ['113', '122'])).
% 2.55/2.80  thf('124', plain, ((l1_struct_0 @ sk_A)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('125', plain,
% 2.55/2.80      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          != (k2_struct_0 @ sk_A)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('demod', [status(thm)], ['123', '124'])).
% 2.55/2.80  thf('126', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['8', '9'])).
% 2.55/2.80  thf('127', plain,
% 2.55/2.80      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          != (k2_struct_0 @ sk_A)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('demod', [status(thm)], ['125', '126'])).
% 2.55/2.80  thf('128', plain,
% 2.55/2.80      (((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.55/2.80           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80           != (k2_struct_0 @ sk_A))
% 2.55/2.80         | ~ (l1_struct_0 @ sk_B)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('sup-', [status(thm)], ['112', '127'])).
% 2.55/2.80  thf('129', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.55/2.80      inference('sup+', [status(thm)], ['8', '9'])).
% 2.55/2.80  thf('130', plain, ((l1_struct_0 @ sk_B)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('131', plain,
% 2.55/2.80      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.55/2.80          != (k2_struct_0 @ sk_A)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('demod', [status(thm)], ['128', '129', '130'])).
% 2.55/2.80  thf('132', plain,
% 2.55/2.80      (![X27 : $i]:
% 2.55/2.80         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 2.55/2.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.55/2.80  thf('133', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.55/2.80      inference('clc', [status(thm)], ['31', '32'])).
% 2.55/2.80  thf('134', plain,
% 2.55/2.80      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 2.55/2.80      inference('sup+', [status(thm)], ['132', '133'])).
% 2.55/2.80  thf('135', plain, ((l1_struct_0 @ sk_A)),
% 2.55/2.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.55/2.80  thf('136', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.55/2.80      inference('demod', [status(thm)], ['134', '135'])).
% 2.55/2.80  thf('137', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.55/2.80      inference('demod', [status(thm)], ['134', '135'])).
% 2.55/2.80  thf('138', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.55/2.80      inference('demod', [status(thm)], ['134', '135'])).
% 2.55/2.80  thf('139', plain,
% 2.55/2.80      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.55/2.80          != (k1_relat_1 @ sk_C)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('demod', [status(thm)], ['131', '136', '137', '138'])).
% 2.55/2.80  thf('140', plain,
% 2.55/2.80      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80          (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('sup-', [status(thm)], ['111', '139'])).
% 2.55/2.80  thf('141', plain,
% 2.55/2.80      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('sup-', [status(thm)], ['101', '140'])).
% 2.55/2.80  thf('142', plain,
% 2.55/2.80      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('sup-', [status(thm)], ['64', '141'])).
% 2.55/2.80  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 2.55/2.80      inference('sup-', [status(thm)], ['20', '21'])).
% 2.55/2.80  thf('144', plain,
% 2.55/2.80      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 2.55/2.80         <= (~
% 2.55/2.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80                = (k2_struct_0 @ sk_A))))),
% 2.55/2.80      inference('demod', [status(thm)], ['142', '143'])).
% 2.55/2.80  thf('145', plain,
% 2.55/2.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          = (k2_struct_0 @ sk_A)))),
% 2.55/2.80      inference('simplify', [status(thm)], ['144'])).
% 2.55/2.80  thf('146', plain,
% 2.55/2.80      (~
% 2.55/2.80       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          = (k2_struct_0 @ sk_B))) | 
% 2.55/2.80       ~
% 2.55/2.80       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          = (k2_struct_0 @ sk_A)))),
% 2.55/2.80      inference('split', [status(esa)], ['1'])).
% 2.55/2.80  thf('147', plain,
% 2.55/2.80      (~
% 2.55/2.80       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.55/2.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.55/2.80          = (k2_struct_0 @ sk_B)))),
% 2.55/2.80      inference('sat_resolution*', [status(thm)], ['145', '146'])).
% 2.55/2.80  thf('148', plain,
% 2.55/2.80      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80         (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('simpl_trail', [status(thm)], ['63', '147'])).
% 2.55/2.80  thf('149', plain,
% 2.55/2.80      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.55/2.80      inference('simplify', [status(thm)], ['98'])).
% 2.55/2.80  thf(t38_relset_1, axiom,
% 2.55/2.80    (![A:$i,B:$i,C:$i]:
% 2.55/2.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.55/2.80       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 2.55/2.80         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.55/2.80  thf('150', plain,
% 2.55/2.80      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.55/2.80         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 2.55/2.80            = (k1_relset_1 @ X16 @ X17 @ X18))
% 2.55/2.80          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.55/2.80      inference('cnf', [status(esa)], [t38_relset_1])).
% 2.55/2.80  thf('151', plain,
% 2.55/2.80      (((k8_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80         (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 2.55/2.80         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80            (k4_relat_1 @ sk_C)))),
% 2.55/2.80      inference('sup-', [status(thm)], ['149', '150'])).
% 2.55/2.80  thf('152', plain,
% 2.55/2.80      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.55/2.80      inference('simplify', [status(thm)], ['98'])).
% 2.55/2.80  thf(redefinition_k8_relset_1, axiom,
% 2.55/2.80    (![A:$i,B:$i,C:$i,D:$i]:
% 2.55/2.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.55/2.80       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.55/2.80  thf('153', plain,
% 2.55/2.80      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.55/2.80         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 2.55/2.80          | ((k8_relset_1 @ X13 @ X14 @ X12 @ X15) = (k10_relat_1 @ X12 @ X15)))),
% 2.55/2.80      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.55/2.80  thf('154', plain,
% 2.55/2.80      (![X0 : $i]:
% 2.55/2.80         ((k8_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80           (k4_relat_1 @ sk_C) @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ X0))),
% 2.55/2.80      inference('sup-', [status(thm)], ['152', '153'])).
% 2.55/2.80  thf('155', plain,
% 2.55/2.80      (((k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 2.55/2.80         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80            (k4_relat_1 @ sk_C)))),
% 2.55/2.80      inference('demod', [status(thm)], ['151', '154'])).
% 2.55/2.80  thf('156', plain,
% 2.55/2.80      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.55/2.80      inference('simplify', [status(thm)], ['98'])).
% 2.55/2.80  thf('157', plain,
% 2.55/2.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.55/2.80         ((v1_relat_1 @ X3)
% 2.55/2.80          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 2.55/2.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.55/2.80  thf('158', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['156', '157'])).
% 2.55/2.80  thf('159', plain,
% 2.55/2.80      (![X1 : $i]:
% 2.55/2.80         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 2.55/2.80          | ~ (v1_relat_1 @ X1))),
% 2.55/2.80      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.55/2.80  thf(t169_relat_1, axiom,
% 2.55/2.80    (![A:$i]:
% 2.55/2.80     ( ( v1_relat_1 @ A ) =>
% 2.55/2.80       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.55/2.80  thf('160', plain,
% 2.55/2.80      (![X0 : $i]:
% 2.55/2.80         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 2.55/2.80          | ~ (v1_relat_1 @ X0))),
% 2.55/2.80      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.55/2.80  thf('161', plain,
% 2.55/2.80      (![X0 : $i]:
% 2.55/2.80         (((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.55/2.80            = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 2.55/2.80          | ~ (v1_relat_1 @ X0)
% 2.55/2.80          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.55/2.80      inference('sup+', [status(thm)], ['159', '160'])).
% 2.55/2.80  thf('162', plain,
% 2.55/2.80      ((~ (v1_relat_1 @ sk_C)
% 2.55/2.80        | ((k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 2.55/2.80            = (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 2.55/2.80      inference('sup-', [status(thm)], ['158', '161'])).
% 2.55/2.80  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 2.55/2.80      inference('sup-', [status(thm)], ['20', '21'])).
% 2.55/2.80  thf('164', plain,
% 2.55/2.80      (((k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 2.55/2.80         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.55/2.80      inference('demod', [status(thm)], ['162', '163'])).
% 2.55/2.80  thf('165', plain,
% 2.55/2.80      (![X1 : $i]:
% 2.55/2.80         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 2.55/2.80          | ~ (v1_relat_1 @ X1))),
% 2.55/2.80      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.55/2.80  thf('166', plain,
% 2.55/2.80      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 2.55/2.80        (k1_zfmisc_1 @ 
% 2.55/2.80         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.55/2.80      inference('simplify', [status(thm)], ['98'])).
% 2.55/2.80  thf('167', plain,
% 2.55/2.80      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.55/2.80         ((v4_relat_1 @ X6 @ X7)
% 2.55/2.80          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.55/2.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.55/2.80  thf('168', plain, ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['166', '167'])).
% 2.55/2.80  thf('169', plain,
% 2.55/2.80      (![X1 : $i]:
% 2.55/2.80         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 2.55/2.80          | ~ (v1_relat_1 @ X1))),
% 2.55/2.80      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.55/2.80  thf('170', plain,
% 2.55/2.80      (![X19 : $i, X20 : $i]:
% 2.55/2.80         (((k1_relat_1 @ X20) != (X19))
% 2.55/2.80          | (v1_partfun1 @ X20 @ X19)
% 2.55/2.80          | ~ (v4_relat_1 @ X20 @ X19)
% 2.55/2.80          | ~ (v1_relat_1 @ X20))),
% 2.55/2.80      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.55/2.80  thf('171', plain,
% 2.55/2.80      (![X20 : $i]:
% 2.55/2.80         (~ (v1_relat_1 @ X20)
% 2.55/2.80          | ~ (v4_relat_1 @ X20 @ (k1_relat_1 @ X20))
% 2.55/2.80          | (v1_partfun1 @ X20 @ (k1_relat_1 @ X20)))),
% 2.55/2.80      inference('simplify', [status(thm)], ['170'])).
% 2.55/2.80  thf('172', plain,
% 2.55/2.80      (![X0 : $i]:
% 2.55/2.80         (~ (v4_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 2.55/2.80          | ~ (v1_relat_1 @ X0)
% 2.55/2.80          | (v1_partfun1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 2.55/2.80          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.55/2.80      inference('sup-', [status(thm)], ['169', '171'])).
% 2.55/2.80  thf('173', plain,
% 2.55/2.80      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.55/2.80        | (v1_partfun1 @ (k4_relat_1 @ sk_C) @ 
% 2.55/2.80           (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 2.55/2.80        | ~ (v1_relat_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['168', '172'])).
% 2.55/2.80  thf('174', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['156', '157'])).
% 2.55/2.80  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 2.55/2.80      inference('sup-', [status(thm)], ['20', '21'])).
% 2.55/2.80  thf('176', plain,
% 2.55/2.80      ((v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.55/2.80      inference('demod', [status(thm)], ['173', '174', '175'])).
% 2.55/2.80  thf('177', plain,
% 2.55/2.80      (((v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.55/2.80        | ~ (v1_relat_1 @ sk_C))),
% 2.55/2.80      inference('sup+', [status(thm)], ['165', '176'])).
% 2.55/2.80  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 2.55/2.80      inference('sup-', [status(thm)], ['20', '21'])).
% 2.55/2.80  thf('179', plain,
% 2.55/2.80      ((v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['177', '178'])).
% 2.55/2.80  thf('180', plain,
% 2.55/2.80      (![X19 : $i, X20 : $i]:
% 2.55/2.80         (~ (v1_partfun1 @ X20 @ X19)
% 2.55/2.80          | ((k1_relat_1 @ X20) = (X19))
% 2.55/2.80          | ~ (v4_relat_1 @ X20 @ X19)
% 2.55/2.80          | ~ (v1_relat_1 @ X20))),
% 2.55/2.80      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.55/2.80  thf('181', plain,
% 2.55/2.80      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.55/2.80        | ~ (v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.55/2.80        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 2.55/2.80      inference('sup-', [status(thm)], ['179', '180'])).
% 2.55/2.80  thf('182', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['156', '157'])).
% 2.55/2.80  thf('183', plain, ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('sup-', [status(thm)], ['166', '167'])).
% 2.55/2.80  thf('184', plain,
% 2.55/2.80      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['181', '182', '183'])).
% 2.55/2.80  thf('185', plain,
% 2.55/2.80      (((k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 2.55/2.80         = (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['164', '184'])).
% 2.55/2.80  thf('186', plain,
% 2.55/2.80      (((k2_relat_1 @ sk_C)
% 2.55/2.80         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.55/2.80            (k4_relat_1 @ sk_C)))),
% 2.55/2.80      inference('demod', [status(thm)], ['155', '185'])).
% 2.55/2.80  thf('187', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 2.55/2.80      inference('demod', [status(thm)], ['148', '186'])).
% 2.55/2.80  thf('188', plain, ($false), inference('simplify', [status(thm)], ['187'])).
% 2.55/2.80  
% 2.55/2.80  % SZS output end Refutation
% 2.55/2.80  
% 2.55/2.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
