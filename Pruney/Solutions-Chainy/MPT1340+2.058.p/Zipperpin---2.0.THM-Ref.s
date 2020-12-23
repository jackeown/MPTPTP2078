%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DdHsZhGe5u

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:16 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  335 (4171 expanded)
%              Number of leaves         :   48 (1227 expanded)
%              Depth                    :   37
%              Number of atoms          : 3035 (93790 expanded)
%              Number of equality atoms :  168 (2936 expanded)
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('13',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('19',plain,(
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

thf('20',plain,(
    ! [X22: $i] :
      ( ( k6_partfun1 @ X22 )
      = ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
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
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','25','26','31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

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

thf('39',plain,(
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

thf('40',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('42',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

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

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('54',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('70',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','58','70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('77',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('79',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('88',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('89',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('90',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
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

thf('92',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != X20 )
      | ( v1_partfun1 @ X21 @ X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('93',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v4_relat_1 @ X21 @ ( k1_relat_1 @ X21 ) )
      | ( v1_partfun1 @ X21 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','103'])).

thf('105',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['87','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('113',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('114',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('117',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41','77','86','114','115','116'])).

thf('118',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('121',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['119','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('130',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

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

thf('133',plain,(
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

thf('134',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf('136',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('138',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X27 ) @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
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
    inference(demod,[status(thm)],['29','30'])).

thf('142',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

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
    inference('sup+',[status(thm)],['2','3'])).

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

thf('150',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('151',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('152',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135','149','152'])).

thf('154',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['118','153'])).

thf('155',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('156',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('157',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('158',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('159',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('160',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('161',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('163',plain,(
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
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
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
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,(
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
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
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
    inference('sup-',[status(thm)],['159','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['158','167'])).

thf('169',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('170',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf('171',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('179',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('180',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('183',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('188',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['180','181','188'])).

thf('190',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('191',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['171','191'])).

thf('193',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('196',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('198',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('199',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('200',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['196','197','200'])).

thf('202',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('203',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['168','169','170','201','202','203','204','205'])).

thf('207',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['157','206'])).

thf('208',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['207','208','209','210'])).

thf('212',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['156','211'])).

thf('213',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('214',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf('215',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('217',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('219',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('221',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['196','197','200'])).

thf('222',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['155','222'])).

thf('224',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['196','197','200'])).

thf('225',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('226',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('227',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['223','224','225','226','227','228'])).

thf('230',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['154','229'])).

thf('231',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('232',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('233',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['231','236'])).

thf('238',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('241',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('242',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('244',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('246',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['242','243','246'])).

thf('248',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['196','197','200'])).

thf('249',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('251',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('252',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['239','249','250','251'])).

thf('253',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('254',plain,(
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

thf('255',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('258',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('260',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['255','256','257','258','259'])).

thf('261',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['252','261'])).

thf('263',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['230','262'])).

thf('264',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','263'])).

thf('265',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('266',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('267',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_funct_2 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['268','269','270'])).

thf('272',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['265','271'])).

thf('273',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('275',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['272','273','274'])).

thf('276',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('277',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['264','275','276','277','278'])).

thf('280',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','279'])).

thf('281',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('282',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['280','281','282'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('284',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('285',plain,(
    $false ),
    inference(demod,[status(thm)],['10','283','284'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DdHsZhGe5u
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 502 iterations in 0.288s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.54/0.75  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.54/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.75  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.54/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.75  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.54/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.75  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.54/0.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.75  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.54/0.75  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.54/0.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.54/0.75  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.54/0.75  thf(t64_tops_2, conjecture,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( l1_struct_0 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.54/0.75           ( ![C:$i]:
% 0.54/0.75             ( ( ( v1_funct_1 @ C ) & 
% 0.54/0.75                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.75                 ( m1_subset_1 @
% 0.54/0.75                   C @ 
% 0.54/0.75                   ( k1_zfmisc_1 @
% 0.54/0.75                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.54/0.75               ( ( ( ( k2_relset_1 @
% 0.54/0.75                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.54/0.75                     ( k2_struct_0 @ B ) ) & 
% 0.54/0.75                   ( v2_funct_1 @ C ) ) =>
% 0.54/0.75                 ( r2_funct_2 @
% 0.54/0.75                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.54/0.75                   ( k2_tops_2 @
% 0.54/0.75                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.54/0.75                     ( k2_tops_2 @
% 0.54/0.75                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.54/0.75                   C ) ) ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i]:
% 0.54/0.75        ( ( l1_struct_0 @ A ) =>
% 0.54/0.75          ( ![B:$i]:
% 0.54/0.75            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.54/0.75              ( ![C:$i]:
% 0.54/0.75                ( ( ( v1_funct_1 @ C ) & 
% 0.54/0.75                    ( v1_funct_2 @
% 0.54/0.75                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.75                    ( m1_subset_1 @
% 0.54/0.75                      C @ 
% 0.54/0.75                      ( k1_zfmisc_1 @
% 0.54/0.75                        ( k2_zfmisc_1 @
% 0.54/0.75                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.54/0.75                  ( ( ( ( k2_relset_1 @
% 0.54/0.75                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.54/0.75                        ( k2_struct_0 @ B ) ) & 
% 0.54/0.75                      ( v2_funct_1 @ C ) ) =>
% 0.54/0.75                    ( r2_funct_2 @
% 0.54/0.75                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.54/0.75                      ( k2_tops_2 @
% 0.54/0.75                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.54/0.75                        ( k2_tops_2 @
% 0.54/0.75                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.54/0.75                      C ) ) ) ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.54/0.75  thf('0', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.75  thf('1', plain,
% 0.54/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.75         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.54/0.75          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75         = (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75         = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf(fc5_struct_0, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.54/0.75       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X34 : $i]:
% 0.54/0.75         (~ (v1_xboole_0 @ (k2_struct_0 @ X34))
% 0.54/0.75          | ~ (l1_struct_0 @ X34)
% 0.54/0.75          | (v2_struct_0 @ X34))),
% 0.54/0.75      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.54/0.75        | (v2_struct_0 @ sk_B)
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.75  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['6', '7'])).
% 0.54/0.75  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf(d3_struct_0, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf(t65_funct_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.75       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X10 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X10)
% 0.54/0.75          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.54/0.75          | ~ (v1_funct_1 @ X10)
% 0.54/0.75          | ~ (v1_relat_1 @ X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_C @ 
% 0.54/0.75         (k1_zfmisc_1 @ 
% 0.54/0.75          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.75  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf(t35_funct_2, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.54/0.75         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.75           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.54/0.75             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.75         (((X30) = (k1_xboole_0))
% 0.54/0.75          | ~ (v1_funct_1 @ X31)
% 0.54/0.75          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 0.54/0.75          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 0.54/0.75          | ((k5_relat_1 @ X31 @ (k2_funct_1 @ X31)) = (k6_partfun1 @ X32))
% 0.54/0.75          | ~ (v2_funct_1 @ X31)
% 0.54/0.75          | ((k2_relset_1 @ X32 @ X30 @ X31) != (X30)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.54/0.75  thf(redefinition_k6_partfun1, axiom,
% 0.54/0.75    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.54/0.75  thf('20', plain, (![X22 : $i]: ((k6_partfun1 @ X22) = (k6_relat_1 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.75         (((X30) = (k1_xboole_0))
% 0.54/0.75          | ~ (v1_funct_1 @ X31)
% 0.54/0.75          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 0.54/0.75          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 0.54/0.75          | ((k5_relat_1 @ X31 @ (k2_funct_1 @ X31)) = (k6_relat_1 @ X32))
% 0.54/0.75          | ~ (v2_funct_1 @ X31)
% 0.54/0.75          | ((k2_relset_1 @ X32 @ X30 @ X31) != (X30)))),
% 0.54/0.75      inference('demod', [status(thm)], ['19', '20'])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75          != (u1_struct_0 @ sk_B))
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.75        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.54/0.75            = (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['18', '21'])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.75         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.54/0.75          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75         = (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.75  thf('26', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('27', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup+', [status(thm)], ['27', '28'])).
% 0.54/0.75  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B))
% 0.54/0.75        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.54/0.75            = (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['22', '25', '26', '31', '32'])).
% 0.54/0.75  thf('34', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B)
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.54/0.75            = (k6_relat_1 @ (k2_struct_0 @ sk_A))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['13', '33'])).
% 0.54/0.75  thf('35', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('37', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.54/0.75            = (k6_relat_1 @ (k2_struct_0 @ sk_A))))),
% 0.54/0.75      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.54/0.75          = (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['37'])).
% 0.54/0.75  thf(t48_funct_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.75           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.54/0.75               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.54/0.75             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X7)
% 0.54/0.75          | ~ (v1_funct_1 @ X7)
% 0.54/0.75          | (v2_funct_1 @ X8)
% 0.54/0.75          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.54/0.75          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.54/0.75          | ~ (v1_funct_1 @ X8)
% 0.54/0.75          | ~ (v1_relat_1 @ X8))),
% 0.54/0.75      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.54/0.75  thf('40', plain,
% 0.54/0.75      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['38', '39'])).
% 0.54/0.75  thf(fc4_funct_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.54/0.75       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.54/0.75  thf('41', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.54/0.75  thf('42', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('43', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('44', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_C @ 
% 0.54/0.75         (k1_zfmisc_1 @ 
% 0.54/0.75          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['42', '43'])).
% 0.54/0.75  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['44', '45'])).
% 0.54/0.75  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('48', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.54/0.75      inference('demod', [status(thm)], ['46', '47'])).
% 0.54/0.75  thf(t31_funct_2, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.54/0.75         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.54/0.75           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.54/0.75           ( m1_subset_1 @
% 0.54/0.75             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.54/0.75  thf('49', plain,
% 0.54/0.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X27)
% 0.54/0.75          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.54/0.75          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 0.54/0.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.54/0.75          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.54/0.75          | ~ (v1_funct_1 @ X27))),
% 0.54/0.75      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.54/0.75  thf('50', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.54/0.75        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75           (k1_zfmisc_1 @ 
% 0.54/0.75            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.54/0.75        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.75            != (k2_relat_1 @ sk_C))
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('52', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('53', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['52', '53'])).
% 0.54/0.75  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('56', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['54', '55'])).
% 0.54/0.75  thf('57', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('58', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.54/0.75  thf('59', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('60', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('61', plain,
% 0.54/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75         = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('62', plain,
% 0.54/0.75      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75          = (k2_struct_0 @ sk_B))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup+', [status(thm)], ['60', '61'])).
% 0.54/0.75  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('64', plain,
% 0.54/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75         = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('65', plain,
% 0.54/0.75      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75          = (k2_struct_0 @ sk_B))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['59', '64'])).
% 0.54/0.75  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('67', plain,
% 0.54/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75         = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['65', '66'])).
% 0.54/0.75  thf('68', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('70', plain,
% 0.54/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.75         = (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.54/0.75  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('72', plain,
% 0.54/0.75      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75         (k1_zfmisc_1 @ 
% 0.54/0.75          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.54/0.75        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.54/0.75      inference('demod', [status(thm)], ['50', '51', '58', '70', '71'])).
% 0.54/0.75  thf('73', plain,
% 0.54/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['72'])).
% 0.54/0.75  thf(cc2_relat_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.75  thf('74', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.54/0.75          | (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.75  thf('75', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ 
% 0.54/0.75           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A)))
% 0.54/0.75        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['73', '74'])).
% 0.54/0.75  thf(fc6_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.75  thf('76', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.75  thf('77', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['75', '76'])).
% 0.54/0.75  thf('78', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.54/0.75      inference('demod', [status(thm)], ['46', '47'])).
% 0.54/0.75  thf('79', plain,
% 0.54/0.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X27)
% 0.54/0.75          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.54/0.75          | (v1_funct_1 @ (k2_funct_1 @ X27))
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.54/0.75          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.54/0.75          | ~ (v1_funct_1 @ X27))),
% 0.54/0.75      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.54/0.75  thf('80', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.54/0.75        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.75            != (k2_relat_1 @ sk_C))
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['78', '79'])).
% 0.54/0.75  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('82', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.54/0.75  thf('83', plain,
% 0.54/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.75         = (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.54/0.75  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('85', plain,
% 0.54/0.75      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.54/0.75      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.54/0.75  thf('86', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('simplify', [status(thm)], ['85'])).
% 0.54/0.75  thf(t55_funct_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.75       ( ( v2_funct_1 @ A ) =>
% 0.54/0.75         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.54/0.75           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.54/0.75  thf('87', plain,
% 0.54/0.75      (![X9 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X9)
% 0.54/0.75          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.54/0.75          | ~ (v1_funct_1 @ X9)
% 0.54/0.75          | ~ (v1_relat_1 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.54/0.75  thf('88', plain,
% 0.54/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['72'])).
% 0.54/0.75  thf(cc2_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.75  thf('89', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.75         ((v4_relat_1 @ X11 @ X12)
% 0.54/0.75          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('90', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['88', '89'])).
% 0.54/0.75  thf('91', plain,
% 0.54/0.75      (![X9 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X9)
% 0.54/0.75          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.54/0.75          | ~ (v1_funct_1 @ X9)
% 0.54/0.75          | ~ (v1_relat_1 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.54/0.75  thf(d4_partfun1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.54/0.75       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.54/0.75  thf('92', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         (((k1_relat_1 @ X21) != (X20))
% 0.54/0.75          | (v1_partfun1 @ X21 @ X20)
% 0.54/0.75          | ~ (v4_relat_1 @ X21 @ X20)
% 0.54/0.75          | ~ (v1_relat_1 @ X21))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.75  thf('93', plain,
% 0.54/0.75      (![X21 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ X21)
% 0.54/0.75          | ~ (v4_relat_1 @ X21 @ (k1_relat_1 @ X21))
% 0.54/0.75          | (v1_partfun1 @ X21 @ (k1_relat_1 @ X21)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['92'])).
% 0.54/0.75  thf('94', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v2_funct_1 @ X0)
% 0.54/0.75          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.54/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['91', '93'])).
% 0.54/0.75  thf('95', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['90', '94'])).
% 0.54/0.75  thf('96', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['75', '76'])).
% 0.54/0.75  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('99', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('100', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.54/0.75          | (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.75  thf('101', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ 
% 0.54/0.75           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.54/0.75        | (v1_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['99', '100'])).
% 0.54/0.75  thf('102', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.75  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('104', plain,
% 0.54/0.75      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.54/0.75      inference('demod', [status(thm)], ['95', '96', '97', '98', '103'])).
% 0.54/0.75  thf('105', plain,
% 0.54/0.75      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.75      inference('sup+', [status(thm)], ['87', '104'])).
% 0.54/0.75  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('109', plain,
% 0.54/0.75      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.54/0.75  thf('110', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         (~ (v1_partfun1 @ X21 @ X20)
% 0.54/0.75          | ((k1_relat_1 @ X21) = (X20))
% 0.54/0.75          | ~ (v4_relat_1 @ X21 @ X20)
% 0.54/0.75          | ~ (v1_relat_1 @ X21))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.75  thf('111', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.54/0.75        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['109', '110'])).
% 0.54/0.75  thf('112', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['75', '76'])).
% 0.54/0.75  thf('113', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['88', '89'])).
% 0.54/0.75  thf('114', plain,
% 0.54/0.75      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.54/0.75  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('117', plain,
% 0.54/0.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.54/0.75        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['40', '41', '77', '86', '114', '115', '116'])).
% 0.54/0.75  thf('118', plain,
% 0.54/0.75      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['117'])).
% 0.54/0.75  thf('119', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('120', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('121', plain,
% 0.54/0.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X27)
% 0.54/0.75          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.54/0.75          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 0.54/0.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.54/0.75          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.54/0.75          | ~ (v1_funct_1 @ X27))),
% 0.54/0.75      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.54/0.75  thf('122', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.75        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75           (k1_zfmisc_1 @ 
% 0.54/0.75            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.54/0.75        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75            != (u1_struct_0 @ sk_B))
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['120', '121'])).
% 0.54/0.75  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('124', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('125', plain,
% 0.54/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75         = (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.75  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('127', plain,
% 0.54/0.75      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75         (k1_zfmisc_1 @ 
% 0.54/0.75          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.54/0.75        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.54/0.75      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.54/0.75  thf('128', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B)
% 0.54/0.75        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75           (k1_zfmisc_1 @ 
% 0.54/0.75            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['119', '127'])).
% 0.54/0.75  thf('129', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('130', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('131', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.54/0.75        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75           (k1_zfmisc_1 @ 
% 0.54/0.75            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.54/0.75      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.54/0.75  thf('132', plain,
% 0.54/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['131'])).
% 0.54/0.75  thf(d4_tops_2, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.54/0.75         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.54/0.75  thf('133', plain,
% 0.54/0.75      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.54/0.75         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 0.54/0.75          | ~ (v2_funct_1 @ X37)
% 0.54/0.75          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 0.54/0.75          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.54/0.75          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.54/0.75          | ~ (v1_funct_1 @ X37))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.54/0.75  thf('134', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75             (k2_struct_0 @ sk_A))
% 0.54/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.75            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.75            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['132', '133'])).
% 0.54/0.75  thf('135', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('simplify', [status(thm)], ['85'])).
% 0.54/0.75  thf('136', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('137', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('138', plain,
% 0.54/0.75      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X27)
% 0.54/0.75          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.54/0.75          | (v1_funct_2 @ (k2_funct_1 @ X27) @ X28 @ X29)
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.54/0.75          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.54/0.75          | ~ (v1_funct_1 @ X27))),
% 0.54/0.75      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.54/0.75  thf('139', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.75        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75           (k2_struct_0 @ sk_A))
% 0.54/0.75        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75            != (u1_struct_0 @ sk_B))
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['137', '138'])).
% 0.54/0.75  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('141', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('142', plain,
% 0.54/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.75         = (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.75  thf('143', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('144', plain,
% 0.54/0.75      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75         (k2_struct_0 @ sk_A))
% 0.54/0.75        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.54/0.75      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 0.54/0.75  thf('145', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B)
% 0.54/0.75        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75           (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['136', '144'])).
% 0.54/0.75  thf('146', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('147', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('148', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.54/0.75        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75           (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.54/0.75  thf('149', plain,
% 0.54/0.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75        (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('simplify', [status(thm)], ['148'])).
% 0.54/0.75  thf('150', plain,
% 0.54/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['131'])).
% 0.54/0.75  thf('151', plain,
% 0.54/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.75         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.54/0.75          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.75  thf('152', plain,
% 0.54/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.75         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['150', '151'])).
% 0.54/0.75  thf('153', plain,
% 0.54/0.75      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.75          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['134', '135', '149', '152'])).
% 0.54/0.75  thf('154', plain,
% 0.54/0.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.54/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.75            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['118', '153'])).
% 0.54/0.75  thf('155', plain,
% 0.54/0.75      (![X9 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X9)
% 0.54/0.75          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.54/0.75          | ~ (v1_funct_1 @ X9)
% 0.54/0.75          | ~ (v1_relat_1 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.54/0.75  thf('156', plain,
% 0.54/0.75      (![X9 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X9)
% 0.54/0.75          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.54/0.75          | ~ (v1_funct_1 @ X9)
% 0.54/0.75          | ~ (v1_relat_1 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.54/0.75  thf('157', plain,
% 0.54/0.75      (![X10 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X10)
% 0.54/0.75          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.54/0.75          | ~ (v1_funct_1 @ X10)
% 0.54/0.75          | ~ (v1_relat_1 @ X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.54/0.75  thf('158', plain,
% 0.54/0.75      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['117'])).
% 0.54/0.75  thf(dt_k2_funct_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.75       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.54/0.75         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.54/0.75  thf('159', plain,
% 0.54/0.75      (![X4 : $i]:
% 0.54/0.75         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.54/0.75          | ~ (v1_funct_1 @ X4)
% 0.54/0.75          | ~ (v1_relat_1 @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.54/0.75  thf('160', plain,
% 0.54/0.75      (![X9 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X9)
% 0.54/0.75          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.54/0.75          | ~ (v1_funct_1 @ X9)
% 0.54/0.75          | ~ (v1_relat_1 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.54/0.75  thf('161', plain,
% 0.54/0.75      (![X10 : $i]:
% 0.54/0.75         (~ (v2_funct_1 @ X10)
% 0.54/0.75          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.54/0.75          | ~ (v1_funct_1 @ X10)
% 0.54/0.75          | ~ (v1_relat_1 @ X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.54/0.75  thf('162', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v2_funct_1 @ X0)
% 0.54/0.75          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.54/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['91', '93'])).
% 0.54/0.75  thf('163', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v2_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.54/0.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.54/0.75             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.54/0.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['161', '162'])).
% 0.54/0.75  thf('164', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v2_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.54/0.75             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.54/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.54/0.75          | ~ (v2_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['160', '163'])).
% 0.54/0.75  thf('165', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.54/0.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.54/0.75             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.54/0.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v2_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['164'])).
% 0.54/0.75  thf('166', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v2_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.54/0.75             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['159', '165'])).
% 0.54/0.75  thf('167', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.54/0.75           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.54/0.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v2_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_relat_1 @ X0)
% 0.54/0.75          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.54/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.54/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['166'])).
% 0.54/0.75  thf('168', plain,
% 0.54/0.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.75        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.54/0.75           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['158', '167'])).
% 0.54/0.75  thf('169', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['75', '76'])).
% 0.54/0.75  thf('170', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('simplify', [status(thm)], ['85'])).
% 0.54/0.75  thf('171', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('172', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('173', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('174', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_C @ 
% 0.54/0.75         (k1_zfmisc_1 @ 
% 0.54/0.75          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['172', '173'])).
% 0.54/0.75  thf('175', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('176', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['174', '175'])).
% 0.54/0.75  thf('177', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('178', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.54/0.75      inference('demod', [status(thm)], ['176', '177'])).
% 0.54/0.75  thf(cc5_funct_2, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.75       ( ![C:$i]:
% 0.54/0.75         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.54/0.75             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.54/0.75  thf('179', plain,
% 0.54/0.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.54/0.75          | (v1_partfun1 @ X17 @ X18)
% 0.54/0.75          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.54/0.75          | ~ (v1_funct_1 @ X17)
% 0.54/0.75          | (v1_xboole_0 @ X19))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.54/0.75  thf('180', plain,
% 0.54/0.75      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.54/0.75        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['178', '179'])).
% 0.54/0.75  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('182', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('183', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('184', plain,
% 0.54/0.75      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['182', '183'])).
% 0.54/0.75  thf('185', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('186', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['184', '185'])).
% 0.54/0.75  thf('187', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('188', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['186', '187'])).
% 0.54/0.75  thf('189', plain,
% 0.54/0.75      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.54/0.75        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['180', '181', '188'])).
% 0.54/0.75  thf('190', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf('191', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.75      inference('clc', [status(thm)], ['189', '190'])).
% 0.54/0.75  thf('192', plain,
% 0.54/0.75      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup+', [status(thm)], ['171', '191'])).
% 0.54/0.75  thf('193', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('194', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['192', '193'])).
% 0.54/0.75  thf('195', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         (~ (v1_partfun1 @ X21 @ X20)
% 0.54/0.75          | ((k1_relat_1 @ X21) = (X20))
% 0.54/0.75          | ~ (v4_relat_1 @ X21 @ X20)
% 0.54/0.75          | ~ (v1_relat_1 @ X21))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.75  thf('196', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['194', '195'])).
% 0.54/0.75  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('198', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('199', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.75         ((v4_relat_1 @ X11 @ X12)
% 0.54/0.75          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('200', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['198', '199'])).
% 0.54/0.75  thf('201', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['196', '197', '200'])).
% 0.54/0.75  thf('202', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['198', '199'])).
% 0.54/0.75  thf('203', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('205', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('206', plain,
% 0.54/0.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.54/0.75           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['168', '169', '170', '201', '202', '203', '204', '205'])).
% 0.54/0.75  thf('207', plain,
% 0.54/0.75      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['157', '206'])).
% 0.54/0.75  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('210', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('211', plain,
% 0.54/0.75      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['207', '208', '209', '210'])).
% 0.54/0.75  thf('212', plain,
% 0.54/0.75      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['156', '211'])).
% 0.54/0.75  thf('213', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['75', '76'])).
% 0.54/0.75  thf('214', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('simplify', [status(thm)], ['85'])).
% 0.54/0.75  thf('215', plain,
% 0.54/0.75      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['212', '213', '214'])).
% 0.54/0.75  thf('216', plain,
% 0.54/0.75      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['117'])).
% 0.54/0.75  thf('217', plain,
% 0.54/0.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.54/0.75      inference('clc', [status(thm)], ['215', '216'])).
% 0.54/0.75  thf('218', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         (~ (v1_partfun1 @ X21 @ X20)
% 0.54/0.75          | ((k1_relat_1 @ X21) = (X20))
% 0.54/0.75          | ~ (v4_relat_1 @ X21 @ X20)
% 0.54/0.75          | ~ (v1_relat_1 @ X21))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.75  thf('219', plain,
% 0.54/0.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['217', '218'])).
% 0.54/0.75  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('221', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['196', '197', '200'])).
% 0.54/0.75  thf('222', plain,
% 0.54/0.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.54/0.75        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.54/0.75      inference('demod', [status(thm)], ['219', '220', '221'])).
% 0.54/0.75  thf('223', plain,
% 0.54/0.75      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.75        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['155', '222'])).
% 0.54/0.75  thf('224', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['196', '197', '200'])).
% 0.54/0.75  thf('225', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['198', '199'])).
% 0.54/0.75  thf('226', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('227', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('228', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('229', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['223', '224', '225', '226', '227', '228'])).
% 0.54/0.75  thf('230', plain,
% 0.54/0.75      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.75          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('clc', [status(thm)], ['154', '229'])).
% 0.54/0.75  thf('231', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('232', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('233', plain,
% 0.54/0.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.54/0.75          sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('234', plain,
% 0.54/0.75      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.54/0.75           sk_C)
% 0.54/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['232', '233'])).
% 0.54/0.75  thf('235', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('236', plain,
% 0.54/0.75      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.54/0.75          sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['234', '235'])).
% 0.54/0.75  thf('237', plain,
% 0.54/0.75      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.54/0.75           sk_C)
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['231', '236'])).
% 0.54/0.75  thf('238', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('239', plain,
% 0.54/0.75      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.54/0.75          sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['237', '238'])).
% 0.54/0.75  thf('240', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.75      inference('clc', [status(thm)], ['189', '190'])).
% 0.54/0.75  thf('241', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         (~ (v1_partfun1 @ X21 @ X20)
% 0.54/0.75          | ((k1_relat_1 @ X21) = (X20))
% 0.54/0.75          | ~ (v4_relat_1 @ X21 @ X20)
% 0.54/0.75          | ~ (v1_relat_1 @ X21))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.75  thf('242', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['240', '241'])).
% 0.54/0.75  thf('243', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('244', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('245', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.75         ((v4_relat_1 @ X11 @ X12)
% 0.54/0.75          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('246', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['244', '245'])).
% 0.54/0.75  thf('247', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['242', '243', '246'])).
% 0.54/0.75  thf('248', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['196', '197', '200'])).
% 0.54/0.75  thf('249', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['247', '248'])).
% 0.54/0.75  thf('250', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['247', '248'])).
% 0.54/0.75  thf('251', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('252', plain,
% 0.54/0.75      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.54/0.75          sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['239', '249', '250', '251'])).
% 0.54/0.75  thf('253', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.54/0.75      inference('demod', [status(thm)], ['46', '47'])).
% 0.54/0.75  thf('254', plain,
% 0.54/0.75      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.54/0.75         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 0.54/0.75          | ~ (v2_funct_1 @ X37)
% 0.54/0.75          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 0.54/0.75          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.54/0.75          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.54/0.75          | ~ (v1_funct_1 @ X37))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.54/0.75  thf('255', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.54/0.75        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.75            = (k2_funct_1 @ sk_C))
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.75        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.75            != (k2_relat_1 @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['253', '254'])).
% 0.54/0.75  thf('256', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('257', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.54/0.75  thf('258', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('259', plain,
% 0.54/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.75         = (k2_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.54/0.75  thf('260', plain,
% 0.54/0.75      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.75          = (k2_funct_1 @ sk_C))
% 0.54/0.75        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.54/0.75      inference('demod', [status(thm)], ['255', '256', '257', '258', '259'])).
% 0.54/0.75  thf('261', plain,
% 0.54/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.75         = (k2_funct_1 @ sk_C))),
% 0.54/0.75      inference('simplify', [status(thm)], ['260'])).
% 0.54/0.75  thf('262', plain,
% 0.54/0.75      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.75           (k2_funct_1 @ sk_C)) @ 
% 0.54/0.75          sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['252', '261'])).
% 0.54/0.75  thf('263', plain,
% 0.54/0.75      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.54/0.75           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['230', '262'])).
% 0.54/0.75  thf('264', plain,
% 0.54/0.75      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.54/0.75           sk_C)
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.75        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['12', '263'])).
% 0.54/0.75  thf('265', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('266', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf(reflexivity_r2_funct_2, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.75         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.54/0.75  thf('267', plain,
% 0.54/0.75      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.54/0.75         ((r2_funct_2 @ X23 @ X24 @ X25 @ X25)
% 0.54/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.54/0.75          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.54/0.75          | ~ (v1_funct_1 @ X25)
% 0.54/0.75          | ~ (v1_funct_1 @ X26)
% 0.54/0.75          | ~ (v1_funct_2 @ X26 @ X23 @ X24)
% 0.54/0.75          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.54/0.75      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.54/0.75  thf('268', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X0 @ 
% 0.54/0.75             (k1_zfmisc_1 @ 
% 0.54/0.75              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.54/0.75          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.75          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.54/0.75             sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['266', '267'])).
% 0.54/0.75  thf('269', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('270', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('271', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X0 @ 
% 0.54/0.75             (k1_zfmisc_1 @ 
% 0.54/0.75              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.54/0.75          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.54/0.75             sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['268', '269', '270'])).
% 0.54/0.75  thf('272', plain,
% 0.54/0.75      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['265', '271'])).
% 0.54/0.75  thf('273', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('274', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('275', plain,
% 0.54/0.75      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['272', '273', '274'])).
% 0.54/0.75  thf('276', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('277', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('278', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('279', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['264', '275', '276', '277', '278'])).
% 0.54/0.75  thf('280', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_B) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['11', '279'])).
% 0.54/0.75  thf('281', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.75      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf('282', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('283', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['280', '281', '282'])).
% 0.54/0.75  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.54/0.75  thf('284', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.75      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.75  thf('285', plain, ($false),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '283', '284'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
