%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RXnGxMB5mA

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:52 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  206 (2303 expanded)
%              Number of leaves         :   38 ( 689 expanded)
%              Depth                    :   29
%              Number of atoms          : 2047 (60395 expanded)
%              Number of equality atoms :  144 (3201 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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

thf('5',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('18',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('22',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','20','21'])).

thf('23',plain,
    ( ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X17 @ X15 )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','38','41'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('43',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('54',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

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

thf('63',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X23 @ X25 )
       != X23 )
      | ~ ( v2_funct_1 @ X25 )
      | ( ( k2_tops_2 @ X24 @ X23 @ X25 )
        = ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('64',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    inference('sup+',[status(thm)],['18','19'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('89',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','74','75','89'])).

thf('91',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

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

thf('93',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('97',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('104',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','52','53','91','102','103'])).

thf('105',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('106',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('107',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('109',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('110',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('113',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != X13 )
      | ( v1_partfun1 @ X14 @ X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('114',plain,(
    ! [X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v4_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
      | ( v1_partfun1 @ X14 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('118',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('119',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('123',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['116','119','120','121','122'])).

thf('124',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['108','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('132',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('133',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','133'])).

thf('135',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('136',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('140',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','145'])).

thf('147',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('150',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('151',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('154',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153'])).

thf('155',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','154'])).

thf('156',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','155'])).

thf('157',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('159',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['157','158'])).

thf('160',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['104','159'])).

thf('161',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,(
    $false ),
    inference(simplify,[status(thm)],['165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RXnGxMB5mA
% 0.15/0.36  % Computer   : n004.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:18:09 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 2.21/2.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.21/2.42  % Solved by: fo/fo7.sh
% 2.21/2.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.21/2.42  % done 297 iterations in 1.942s
% 2.21/2.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.21/2.42  % SZS output start Refutation
% 2.21/2.42  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.21/2.42  thf(sk_B_type, type, sk_B: $i).
% 2.21/2.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.21/2.42  thf(sk_C_type, type, sk_C: $i).
% 2.21/2.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.21/2.42  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.21/2.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.21/2.42  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.21/2.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.21/2.42  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.21/2.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.21/2.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.21/2.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.21/2.42  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.21/2.42  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.21/2.42  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.21/2.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.21/2.42  thf(sk_A_type, type, sk_A: $i).
% 2.21/2.42  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.21/2.42  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.21/2.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.21/2.42  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.21/2.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.21/2.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.21/2.42  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 2.21/2.42  thf(t55_funct_1, axiom,
% 2.21/2.42    (![A:$i]:
% 2.21/2.42     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.21/2.42       ( ( v2_funct_1 @ A ) =>
% 2.21/2.42         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.21/2.42           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.21/2.42  thf('0', plain,
% 2.21/2.42      (![X0 : $i]:
% 2.21/2.42         (~ (v2_funct_1 @ X0)
% 2.21/2.42          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.21/2.42          | ~ (v1_funct_1 @ X0)
% 2.21/2.42          | ~ (v1_relat_1 @ X0))),
% 2.21/2.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.21/2.42  thf(d3_struct_0, axiom,
% 2.21/2.42    (![A:$i]:
% 2.21/2.42     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.21/2.42  thf('1', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('2', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('3', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('4', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf(t62_tops_2, conjecture,
% 2.21/2.42    (![A:$i]:
% 2.21/2.42     ( ( l1_struct_0 @ A ) =>
% 2.21/2.42       ( ![B:$i]:
% 2.21/2.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.21/2.42           ( ![C:$i]:
% 2.21/2.42             ( ( ( v1_funct_1 @ C ) & 
% 2.21/2.42                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.21/2.42                 ( m1_subset_1 @
% 2.21/2.42                   C @ 
% 2.21/2.42                   ( k1_zfmisc_1 @
% 2.21/2.42                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.21/2.42               ( ( ( ( k2_relset_1 @
% 2.21/2.42                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.21/2.42                     ( k2_struct_0 @ B ) ) & 
% 2.21/2.42                   ( v2_funct_1 @ C ) ) =>
% 2.21/2.42                 ( ( ( k1_relset_1 @
% 2.21/2.42                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.21/2.42                       ( k2_tops_2 @
% 2.21/2.42                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.21/2.42                     ( k2_struct_0 @ B ) ) & 
% 2.21/2.42                   ( ( k2_relset_1 @
% 2.21/2.42                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.21/2.42                       ( k2_tops_2 @
% 2.21/2.42                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.21/2.42                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 2.21/2.42  thf(zf_stmt_0, negated_conjecture,
% 2.21/2.42    (~( ![A:$i]:
% 2.21/2.42        ( ( l1_struct_0 @ A ) =>
% 2.21/2.42          ( ![B:$i]:
% 2.21/2.42            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.21/2.42              ( ![C:$i]:
% 2.21/2.42                ( ( ( v1_funct_1 @ C ) & 
% 2.21/2.42                    ( v1_funct_2 @
% 2.21/2.42                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.21/2.42                    ( m1_subset_1 @
% 2.21/2.42                      C @ 
% 2.21/2.42                      ( k1_zfmisc_1 @
% 2.21/2.42                        ( k2_zfmisc_1 @
% 2.21/2.42                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.21/2.42                  ( ( ( ( k2_relset_1 @
% 2.21/2.42                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.21/2.42                        ( k2_struct_0 @ B ) ) & 
% 2.21/2.42                      ( v2_funct_1 @ C ) ) =>
% 2.21/2.42                    ( ( ( k1_relset_1 @
% 2.21/2.42                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.21/2.42                          ( k2_tops_2 @
% 2.21/2.42                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.21/2.42                        ( k2_struct_0 @ B ) ) & 
% 2.21/2.42                      ( ( k2_relset_1 @
% 2.21/2.42                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.21/2.42                          ( k2_tops_2 @
% 2.21/2.42                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.21/2.42                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 2.21/2.42    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 2.21/2.42  thf('5', plain,
% 2.21/2.42      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_B))
% 2.21/2.42        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42            != (k2_struct_0 @ sk_A)))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('6', plain,
% 2.21/2.42      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_A)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('split', [status(esa)], ['5'])).
% 2.21/2.42  thf('7', plain,
% 2.21/2.42      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42           != (k2_struct_0 @ sk_A))
% 2.21/2.42         | ~ (l1_struct_0 @ sk_A)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('sup-', [status(thm)], ['4', '6'])).
% 2.21/2.42  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('9', plain,
% 2.21/2.42      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_A)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('demod', [status(thm)], ['7', '8'])).
% 2.21/2.42  thf('10', plain,
% 2.21/2.42      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42           != (k2_struct_0 @ sk_A))
% 2.21/2.42         | ~ (l1_struct_0 @ sk_B)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('sup-', [status(thm)], ['3', '9'])).
% 2.21/2.42  thf('11', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('12', plain,
% 2.21/2.42      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_A)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('demod', [status(thm)], ['10', '11'])).
% 2.21/2.42  thf('13', plain,
% 2.21/2.42      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42           != (k2_struct_0 @ sk_A))
% 2.21/2.42         | ~ (l1_struct_0 @ sk_B)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('sup-', [status(thm)], ['2', '12'])).
% 2.21/2.42  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('15', plain,
% 2.21/2.42      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_A)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('demod', [status(thm)], ['13', '14'])).
% 2.21/2.42  thf('16', plain,
% 2.21/2.42      ((m1_subset_1 @ sk_C @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf(redefinition_k2_relset_1, axiom,
% 2.21/2.42    (![A:$i,B:$i,C:$i]:
% 2.21/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.21/2.42       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.21/2.42  thf('17', plain,
% 2.21/2.42      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.21/2.42         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 2.21/2.42          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.21/2.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.21/2.42  thf('18', plain,
% 2.21/2.42      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.42         = (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('sup-', [status(thm)], ['16', '17'])).
% 2.21/2.42  thf('19', plain,
% 2.21/2.42      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.42         = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('20', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.21/2.42  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.21/2.42  thf('22', plain,
% 2.21/2.42      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_A)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('demod', [status(thm)], ['15', '20', '21'])).
% 2.21/2.42  thf('23', plain,
% 2.21/2.42      (((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.42           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.21/2.42           != (k2_struct_0 @ sk_A))
% 2.21/2.42         | ~ (l1_struct_0 @ sk_A)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('sup-', [status(thm)], ['1', '22'])).
% 2.21/2.42  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('25', plain,
% 2.21/2.42      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_A)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('demod', [status(thm)], ['23', '24'])).
% 2.21/2.42  thf('26', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('27', plain,
% 2.21/2.42      ((m1_subset_1 @ sk_C @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf(t132_funct_2, axiom,
% 2.21/2.42    (![A:$i,B:$i,C:$i]:
% 2.21/2.42     ( ( ( v1_funct_1 @ C ) & 
% 2.21/2.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.21/2.42       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.21/2.42           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.21/2.42         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.21/2.42           ( v1_partfun1 @ C @ A ) ) ) ))).
% 2.21/2.42  thf('28', plain,
% 2.21/2.42      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.21/2.42         (((X15) = (k1_xboole_0))
% 2.21/2.42          | ~ (v1_funct_1 @ X16)
% 2.21/2.42          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 2.21/2.42          | (v1_partfun1 @ X16 @ X17)
% 2.21/2.42          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 2.21/2.42          | ~ (v1_funct_2 @ X16 @ X17 @ X15)
% 2.21/2.42          | ~ (v1_funct_1 @ X16))),
% 2.21/2.42      inference('cnf', [status(esa)], [t132_funct_2])).
% 2.21/2.42  thf('29', plain,
% 2.21/2.42      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.21/2.42         (~ (v1_funct_2 @ X16 @ X17 @ X15)
% 2.21/2.42          | (v1_partfun1 @ X16 @ X17)
% 2.21/2.42          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X15)))
% 2.21/2.42          | ~ (v1_funct_1 @ X16)
% 2.21/2.42          | ((X15) = (k1_xboole_0)))),
% 2.21/2.42      inference('simplify', [status(thm)], ['28'])).
% 2.21/2.42  thf('30', plain,
% 2.21/2.42      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.21/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.21/2.42        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.21/2.42        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 2.21/2.42      inference('sup-', [status(thm)], ['27', '29'])).
% 2.21/2.42  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('32', plain,
% 2.21/2.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('33', plain,
% 2.21/2.42      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.21/2.42        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 2.21/2.42      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.21/2.42  thf(d4_partfun1, axiom,
% 2.21/2.42    (![A:$i,B:$i]:
% 2.21/2.42     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.21/2.42       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 2.21/2.42  thf('34', plain,
% 2.21/2.42      (![X13 : $i, X14 : $i]:
% 2.21/2.42         (~ (v1_partfun1 @ X14 @ X13)
% 2.21/2.42          | ((k1_relat_1 @ X14) = (X13))
% 2.21/2.42          | ~ (v4_relat_1 @ X14 @ X13)
% 2.21/2.42          | ~ (v1_relat_1 @ X14))),
% 2.21/2.42      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.21/2.42  thf('35', plain,
% 2.21/2.42      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.21/2.42        | ~ (v1_relat_1 @ sk_C)
% 2.21/2.42        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 2.21/2.42        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.21/2.42      inference('sup-', [status(thm)], ['33', '34'])).
% 2.21/2.42  thf('36', plain,
% 2.21/2.42      ((m1_subset_1 @ sk_C @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf(cc1_relset_1, axiom,
% 2.21/2.42    (![A:$i,B:$i,C:$i]:
% 2.21/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.21/2.42       ( v1_relat_1 @ C ) ))).
% 2.21/2.42  thf('37', plain,
% 2.21/2.42      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.21/2.42         ((v1_relat_1 @ X1)
% 2.21/2.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 2.21/2.42      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.21/2.42  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.42      inference('sup-', [status(thm)], ['36', '37'])).
% 2.21/2.42  thf('39', plain,
% 2.21/2.42      ((m1_subset_1 @ sk_C @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf(cc2_relset_1, axiom,
% 2.21/2.42    (![A:$i,B:$i,C:$i]:
% 2.21/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.21/2.42       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.21/2.42  thf('40', plain,
% 2.21/2.42      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.21/2.42         ((v4_relat_1 @ X4 @ X5)
% 2.21/2.42          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 2.21/2.42      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.21/2.42  thf('41', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 2.21/2.42      inference('sup-', [status(thm)], ['39', '40'])).
% 2.21/2.42  thf('42', plain,
% 2.21/2.42      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.21/2.42        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 2.21/2.42      inference('demod', [status(thm)], ['35', '38', '41'])).
% 2.21/2.42  thf(fc2_struct_0, axiom,
% 2.21/2.42    (![A:$i]:
% 2.21/2.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.21/2.42       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.21/2.42  thf('43', plain,
% 2.21/2.42      (![X22 : $i]:
% 2.21/2.42         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 2.21/2.42          | ~ (l1_struct_0 @ X22)
% 2.21/2.42          | (v2_struct_0 @ X22))),
% 2.21/2.42      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.21/2.42  thf('44', plain,
% 2.21/2.42      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.21/2.42        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 2.21/2.42        | (v2_struct_0 @ sk_B)
% 2.21/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup-', [status(thm)], ['42', '43'])).
% 2.21/2.42  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.21/2.42  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.21/2.42      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.21/2.42  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('47', plain,
% 2.21/2.42      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 2.21/2.42      inference('demod', [status(thm)], ['44', '45', '46'])).
% 2.21/2.42  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('49', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.21/2.42      inference('clc', [status(thm)], ['47', '48'])).
% 2.21/2.42  thf('50', plain,
% 2.21/2.42      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 2.21/2.42      inference('sup+', [status(thm)], ['26', '49'])).
% 2.21/2.42  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('52', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.21/2.42      inference('demod', [status(thm)], ['50', '51'])).
% 2.21/2.42  thf('53', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.21/2.42      inference('demod', [status(thm)], ['50', '51'])).
% 2.21/2.42  thf('54', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('55', plain,
% 2.21/2.42      ((m1_subset_1 @ sk_C @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('56', plain,
% 2.21/2.42      (((m1_subset_1 @ sk_C @ 
% 2.21/2.42         (k1_zfmisc_1 @ 
% 2.21/2.42          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 2.21/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['54', '55'])).
% 2.21/2.42  thf('57', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('58', plain,
% 2.21/2.42      ((m1_subset_1 @ sk_C @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('demod', [status(thm)], ['56', '57'])).
% 2.21/2.42  thf('59', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.21/2.42  thf('60', plain,
% 2.21/2.42      ((m1_subset_1 @ sk_C @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.21/2.42      inference('demod', [status(thm)], ['58', '59'])).
% 2.21/2.42  thf('61', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.21/2.42      inference('clc', [status(thm)], ['47', '48'])).
% 2.21/2.42  thf('62', plain,
% 2.21/2.42      ((m1_subset_1 @ sk_C @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.21/2.42      inference('demod', [status(thm)], ['60', '61'])).
% 2.21/2.42  thf(d4_tops_2, axiom,
% 2.21/2.42    (![A:$i,B:$i,C:$i]:
% 2.21/2.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.21/2.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.21/2.42       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.21/2.42         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 2.21/2.42  thf('63', plain,
% 2.21/2.42      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.21/2.42         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 2.21/2.42          | ~ (v2_funct_1 @ X25)
% 2.21/2.42          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 2.21/2.42          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 2.21/2.42          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 2.21/2.42          | ~ (v1_funct_1 @ X25))),
% 2.21/2.42      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.21/2.42  thf('64', plain,
% 2.21/2.42      ((~ (v1_funct_1 @ sk_C)
% 2.21/2.42        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.21/2.42        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.42            = (k2_funct_1 @ sk_C))
% 2.21/2.42        | ~ (v2_funct_1 @ sk_C)
% 2.21/2.42        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.42            != (k2_relat_1 @ sk_C)))),
% 2.21/2.42      inference('sup-', [status(thm)], ['62', '63'])).
% 2.21/2.42  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('66', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('67', plain,
% 2.21/2.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('68', plain,
% 2.21/2.42      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.21/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['66', '67'])).
% 2.21/2.42  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('70', plain,
% 2.21/2.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('demod', [status(thm)], ['68', '69'])).
% 2.21/2.42  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.21/2.42  thf('72', plain,
% 2.21/2.42      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['70', '71'])).
% 2.21/2.42  thf('73', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.21/2.42      inference('clc', [status(thm)], ['47', '48'])).
% 2.21/2.42  thf('74', plain,
% 2.21/2.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['72', '73'])).
% 2.21/2.42  thf('75', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('76', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('77', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('78', plain,
% 2.21/2.42      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.42         = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('79', plain,
% 2.21/2.42      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.42          = (k2_struct_0 @ sk_B))
% 2.21/2.42        | ~ (l1_struct_0 @ sk_A))),
% 2.21/2.42      inference('sup+', [status(thm)], ['77', '78'])).
% 2.21/2.42  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('81', plain,
% 2.21/2.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.42         = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('demod', [status(thm)], ['79', '80'])).
% 2.21/2.42  thf('82', plain,
% 2.21/2.42      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.21/2.42          = (k2_struct_0 @ sk_B))
% 2.21/2.42        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['76', '81'])).
% 2.21/2.42  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('84', plain,
% 2.21/2.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.21/2.42         = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('demod', [status(thm)], ['82', '83'])).
% 2.21/2.42  thf('85', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.21/2.42  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.21/2.42  thf('87', plain,
% 2.21/2.42      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.42         = (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['84', '85', '86'])).
% 2.21/2.42  thf('88', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.21/2.42      inference('demod', [status(thm)], ['50', '51'])).
% 2.21/2.42  thf('89', plain,
% 2.21/2.42      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.42         = (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['87', '88'])).
% 2.21/2.42  thf('90', plain,
% 2.21/2.42      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.42          = (k2_funct_1 @ sk_C))
% 2.21/2.42        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.21/2.42      inference('demod', [status(thm)], ['64', '65', '74', '75', '89'])).
% 2.21/2.42  thf('91', plain,
% 2.21/2.42      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.42         = (k2_funct_1 @ sk_C))),
% 2.21/2.42      inference('simplify', [status(thm)], ['90'])).
% 2.21/2.42  thf('92', plain,
% 2.21/2.42      ((m1_subset_1 @ sk_C @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 2.21/2.42      inference('demod', [status(thm)], ['60', '61'])).
% 2.21/2.42  thf(t31_funct_2, axiom,
% 2.21/2.42    (![A:$i,B:$i,C:$i]:
% 2.21/2.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.21/2.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.21/2.42       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.21/2.42         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.21/2.42           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.21/2.42           ( m1_subset_1 @
% 2.21/2.42             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.21/2.42  thf('93', plain,
% 2.21/2.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.21/2.42         (~ (v2_funct_1 @ X18)
% 2.21/2.42          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 2.21/2.42          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 2.21/2.42             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.21/2.42          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 2.21/2.42          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 2.21/2.42          | ~ (v1_funct_1 @ X18))),
% 2.21/2.42      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.21/2.42  thf('94', plain,
% 2.21/2.42      ((~ (v1_funct_1 @ sk_C)
% 2.21/2.42        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.21/2.42        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.42           (k1_zfmisc_1 @ 
% 2.21/2.42            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 2.21/2.42        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.42            != (k2_relat_1 @ sk_C))
% 2.21/2.42        | ~ (v2_funct_1 @ sk_C))),
% 2.21/2.42      inference('sup-', [status(thm)], ['92', '93'])).
% 2.21/2.42  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('96', plain,
% 2.21/2.42      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['72', '73'])).
% 2.21/2.42  thf('97', plain,
% 2.21/2.42      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.42         = (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['87', '88'])).
% 2.21/2.42  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('99', plain,
% 2.21/2.42      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.42         (k1_zfmisc_1 @ 
% 2.21/2.42          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 2.21/2.42        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.21/2.42      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 2.21/2.42  thf('100', plain,
% 2.21/2.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.21/2.42      inference('simplify', [status(thm)], ['99'])).
% 2.21/2.42  thf('101', plain,
% 2.21/2.42      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.21/2.42         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 2.21/2.42          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.21/2.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.21/2.42  thf('102', plain,
% 2.21/2.42      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.21/2.42         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.21/2.42      inference('sup-', [status(thm)], ['100', '101'])).
% 2.21/2.42  thf('103', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.21/2.42      inference('demod', [status(thm)], ['50', '51'])).
% 2.21/2.42  thf('104', plain,
% 2.21/2.42      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_A))))),
% 2.21/2.42      inference('demod', [status(thm)], ['25', '52', '53', '91', '102', '103'])).
% 2.21/2.42  thf('105', plain,
% 2.21/2.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.21/2.42      inference('simplify', [status(thm)], ['99'])).
% 2.21/2.42  thf(redefinition_k1_relset_1, axiom,
% 2.21/2.42    (![A:$i,B:$i,C:$i]:
% 2.21/2.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.21/2.42       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.21/2.42  thf('106', plain,
% 2.21/2.42      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.21/2.42         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 2.21/2.42          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.21/2.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.21/2.42  thf('107', plain,
% 2.21/2.42      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.21/2.42         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.21/2.42      inference('sup-', [status(thm)], ['105', '106'])).
% 2.21/2.42  thf('108', plain,
% 2.21/2.42      (![X0 : $i]:
% 2.21/2.42         (~ (v2_funct_1 @ X0)
% 2.21/2.42          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.21/2.42          | ~ (v1_funct_1 @ X0)
% 2.21/2.42          | ~ (v1_relat_1 @ X0))),
% 2.21/2.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.21/2.42  thf('109', plain,
% 2.21/2.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.21/2.42      inference('simplify', [status(thm)], ['99'])).
% 2.21/2.42  thf('110', plain,
% 2.21/2.42      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.21/2.42         ((v4_relat_1 @ X4 @ X5)
% 2.21/2.42          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 2.21/2.42      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.21/2.42  thf('111', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('sup-', [status(thm)], ['109', '110'])).
% 2.21/2.42  thf('112', plain,
% 2.21/2.42      (![X0 : $i]:
% 2.21/2.42         (~ (v2_funct_1 @ X0)
% 2.21/2.42          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.21/2.42          | ~ (v1_funct_1 @ X0)
% 2.21/2.42          | ~ (v1_relat_1 @ X0))),
% 2.21/2.42      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.21/2.42  thf('113', plain,
% 2.21/2.42      (![X13 : $i, X14 : $i]:
% 2.21/2.42         (((k1_relat_1 @ X14) != (X13))
% 2.21/2.42          | (v1_partfun1 @ X14 @ X13)
% 2.21/2.42          | ~ (v4_relat_1 @ X14 @ X13)
% 2.21/2.42          | ~ (v1_relat_1 @ X14))),
% 2.21/2.42      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.21/2.42  thf('114', plain,
% 2.21/2.42      (![X14 : $i]:
% 2.21/2.42         (~ (v1_relat_1 @ X14)
% 2.21/2.42          | ~ (v4_relat_1 @ X14 @ (k1_relat_1 @ X14))
% 2.21/2.42          | (v1_partfun1 @ X14 @ (k1_relat_1 @ X14)))),
% 2.21/2.42      inference('simplify', [status(thm)], ['113'])).
% 2.21/2.42  thf('115', plain,
% 2.21/2.42      (![X0 : $i]:
% 2.21/2.42         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.21/2.42          | ~ (v1_relat_1 @ X0)
% 2.21/2.42          | ~ (v1_funct_1 @ X0)
% 2.21/2.42          | ~ (v2_funct_1 @ X0)
% 2.21/2.42          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.21/2.42          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.21/2.42      inference('sup-', [status(thm)], ['112', '114'])).
% 2.21/2.42  thf('116', plain,
% 2.21/2.42      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.21/2.42        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.42           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.21/2.42        | ~ (v2_funct_1 @ sk_C)
% 2.21/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.21/2.42        | ~ (v1_relat_1 @ sk_C))),
% 2.21/2.42      inference('sup-', [status(thm)], ['111', '115'])).
% 2.21/2.42  thf('117', plain,
% 2.21/2.42      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.42        (k1_zfmisc_1 @ 
% 2.21/2.42         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 2.21/2.42      inference('simplify', [status(thm)], ['99'])).
% 2.21/2.42  thf('118', plain,
% 2.21/2.42      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.21/2.42         ((v1_relat_1 @ X1)
% 2.21/2.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 2.21/2.42      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.21/2.42  thf('119', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.21/2.42      inference('sup-', [status(thm)], ['117', '118'])).
% 2.21/2.42  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('122', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.42      inference('sup-', [status(thm)], ['36', '37'])).
% 2.21/2.42  thf('123', plain,
% 2.21/2.42      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.21/2.42      inference('demod', [status(thm)], ['116', '119', '120', '121', '122'])).
% 2.21/2.42  thf('124', plain,
% 2.21/2.42      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.21/2.42        | ~ (v1_relat_1 @ sk_C)
% 2.21/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.21/2.42        | ~ (v2_funct_1 @ sk_C))),
% 2.21/2.42      inference('sup+', [status(thm)], ['108', '123'])).
% 2.21/2.42  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.42      inference('sup-', [status(thm)], ['36', '37'])).
% 2.21/2.42  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('128', plain,
% 2.21/2.42      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 2.21/2.42  thf('129', plain,
% 2.21/2.42      (![X13 : $i, X14 : $i]:
% 2.21/2.42         (~ (v1_partfun1 @ X14 @ X13)
% 2.21/2.42          | ((k1_relat_1 @ X14) = (X13))
% 2.21/2.42          | ~ (v4_relat_1 @ X14 @ X13)
% 2.21/2.42          | ~ (v1_relat_1 @ X14))),
% 2.21/2.42      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.21/2.42  thf('130', plain,
% 2.21/2.42      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.21/2.42        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.21/2.42        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 2.21/2.42      inference('sup-', [status(thm)], ['128', '129'])).
% 2.21/2.42  thf('131', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.21/2.42      inference('sup-', [status(thm)], ['117', '118'])).
% 2.21/2.42  thf('132', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('sup-', [status(thm)], ['109', '110'])).
% 2.21/2.42  thf('133', plain,
% 2.21/2.42      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['130', '131', '132'])).
% 2.21/2.42  thf('134', plain,
% 2.21/2.42      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.21/2.42         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['107', '133'])).
% 2.21/2.42  thf('135', plain,
% 2.21/2.42      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.42         = (k2_funct_1 @ sk_C))),
% 2.21/2.42      inference('simplify', [status(thm)], ['90'])).
% 2.21/2.42  thf('136', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('137', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('138', plain,
% 2.21/2.42      (![X21 : $i]:
% 2.21/2.42         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 2.21/2.42      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.42  thf('139', plain,
% 2.21/2.42      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_B)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('split', [status(esa)], ['5'])).
% 2.21/2.42  thf('140', plain,
% 2.21/2.42      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42           != (k2_struct_0 @ sk_B))
% 2.21/2.42         | ~ (l1_struct_0 @ sk_B)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('sup-', [status(thm)], ['138', '139'])).
% 2.21/2.42  thf('141', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('142', plain,
% 2.21/2.42      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_B)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('demod', [status(thm)], ['140', '141'])).
% 2.21/2.42  thf('143', plain,
% 2.21/2.42      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.42           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42           != (k2_struct_0 @ sk_B))
% 2.21/2.42         | ~ (l1_struct_0 @ sk_A)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('sup-', [status(thm)], ['137', '142'])).
% 2.21/2.42  thf('144', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('145', plain,
% 2.21/2.42      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_B)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('demod', [status(thm)], ['143', '144'])).
% 2.21/2.42  thf('146', plain,
% 2.21/2.42      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.42           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42           != (k2_struct_0 @ sk_B))
% 2.21/2.42         | ~ (l1_struct_0 @ sk_B)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('sup-', [status(thm)], ['136', '145'])).
% 2.21/2.42  thf('147', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('148', plain,
% 2.21/2.42      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          != (k2_struct_0 @ sk_B)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('demod', [status(thm)], ['146', '147'])).
% 2.21/2.42  thf('149', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.21/2.42  thf('150', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 2.21/2.42      inference('demod', [status(thm)], ['50', '51'])).
% 2.21/2.42  thf('151', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 2.21/2.42      inference('clc', [status(thm)], ['47', '48'])).
% 2.21/2.42  thf('152', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.21/2.42  thf('153', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.42      inference('sup+', [status(thm)], ['18', '19'])).
% 2.21/2.42  thf('154', plain,
% 2.21/2.42      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.21/2.42          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.21/2.42          != (k2_relat_1 @ sk_C)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('demod', [status(thm)],
% 2.21/2.42                ['148', '149', '150', '151', '152', '153'])).
% 2.21/2.42  thf('155', plain,
% 2.21/2.42      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 2.21/2.42          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('sup-', [status(thm)], ['135', '154'])).
% 2.21/2.42  thf('156', plain,
% 2.21/2.42      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 2.21/2.42         <= (~
% 2.21/2.42             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42                = (k2_struct_0 @ sk_B))))),
% 2.21/2.42      inference('sup-', [status(thm)], ['134', '155'])).
% 2.21/2.42  thf('157', plain,
% 2.21/2.42      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          = (k2_struct_0 @ sk_B)))),
% 2.21/2.42      inference('simplify', [status(thm)], ['156'])).
% 2.21/2.42  thf('158', plain,
% 2.21/2.42      (~
% 2.21/2.42       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          = (k2_struct_0 @ sk_A))) | 
% 2.21/2.42       ~
% 2.21/2.42       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          = (k2_struct_0 @ sk_B)))),
% 2.21/2.42      inference('split', [status(esa)], ['5'])).
% 2.21/2.42  thf('159', plain,
% 2.21/2.42      (~
% 2.21/2.42       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.42          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.42          = (k2_struct_0 @ sk_A)))),
% 2.21/2.42      inference('sat_resolution*', [status(thm)], ['157', '158'])).
% 2.21/2.42  thf('160', plain,
% 2.21/2.42      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 2.21/2.42      inference('simpl_trail', [status(thm)], ['104', '159'])).
% 2.21/2.42  thf('161', plain,
% 2.21/2.42      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 2.21/2.42        | ~ (v1_relat_1 @ sk_C)
% 2.21/2.42        | ~ (v1_funct_1 @ sk_C)
% 2.21/2.42        | ~ (v2_funct_1 @ sk_C))),
% 2.21/2.42      inference('sup-', [status(thm)], ['0', '160'])).
% 2.21/2.42  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.42      inference('sup-', [status(thm)], ['36', '37'])).
% 2.21/2.42  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.42  thf('165', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 2.21/2.42      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 2.21/2.42  thf('166', plain, ($false), inference('simplify', [status(thm)], ['165'])).
% 2.21/2.42  
% 2.21/2.42  % SZS output end Refutation
% 2.21/2.42  
% 2.21/2.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
