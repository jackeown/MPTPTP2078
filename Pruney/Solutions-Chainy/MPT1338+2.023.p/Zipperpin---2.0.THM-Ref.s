%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M3VLne1v8O

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:50 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  217 (3565 expanded)
%              Number of leaves         :   36 (1032 expanded)
%              Depth                    :   30
%              Number of atoms          : 1972 (90279 expanded)
%              Number of equality atoms :  126 (4572 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('33',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','41'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('59',plain,(
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

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','41'])).

thf('75',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('81',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('87',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','88'])).

thf('90',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('99',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['91','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','61','89','90','104'])).

thf('106',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('108',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','88'])).

thf('112',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf('119',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','51','52','53','106','117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('121',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('122',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('124',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('125',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('126',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('128',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != X16 )
      | ( v1_partfun1 @ X17 @ X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('129',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v4_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
      | ( v1_partfun1 @ X17 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','129'])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('133',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('134',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('138',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','134','135','136','137'])).

thf('139',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['123','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('145',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('147',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('148',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','148'])).

thf('150',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('151',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('153',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('154',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('155',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','157'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('160',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('162',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('163',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','163'])).

thf('165',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','164'])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('167',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','168'])).

thf('170',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('172',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['170','171'])).

thf('173',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['119','172'])).

thf('174',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176','177'])).

thf('179',plain,(
    $false ),
    inference(simplify,[status(thm)],['178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M3VLne1v8O
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.83  % Solved by: fo/fo7.sh
% 1.65/1.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.83  % done 304 iterations in 1.376s
% 1.65/1.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.83  % SZS output start Refutation
% 1.65/1.83  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.65/1.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.65/1.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.65/1.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.83  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.65/1.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.65/1.83  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.83  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.83  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.65/1.83  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.65/1.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.83  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.65/1.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.65/1.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.65/1.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.83  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.65/1.83  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.65/1.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.83  thf(t55_funct_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.83       ( ( v2_funct_1 @ A ) =>
% 1.65/1.83         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.65/1.83           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.65/1.83  thf('0', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v2_funct_1 @ X0)
% 1.65/1.83          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.83          | ~ (v1_funct_1 @ X0)
% 1.65/1.83          | ~ (v1_relat_1 @ X0))),
% 1.65/1.83      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.83  thf(d3_struct_0, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.65/1.83  thf('1', plain,
% 1.65/1.83      (![X21 : $i]:
% 1.65/1.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.83  thf('2', plain,
% 1.65/1.83      (![X21 : $i]:
% 1.65/1.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.83  thf(t62_tops_2, conjecture,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( l1_struct_0 @ A ) =>
% 1.65/1.83       ( ![B:$i]:
% 1.65/1.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.65/1.83           ( ![C:$i]:
% 1.65/1.83             ( ( ( v1_funct_1 @ C ) & 
% 1.65/1.83                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.83                 ( m1_subset_1 @
% 1.65/1.83                   C @ 
% 1.65/1.83                   ( k1_zfmisc_1 @
% 1.65/1.83                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.83               ( ( ( ( k2_relset_1 @
% 1.65/1.83                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.65/1.83                     ( k2_struct_0 @ B ) ) & 
% 1.65/1.83                   ( v2_funct_1 @ C ) ) =>
% 1.65/1.83                 ( ( ( k1_relset_1 @
% 1.65/1.83                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.65/1.83                       ( k2_tops_2 @
% 1.65/1.83                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.65/1.83                     ( k2_struct_0 @ B ) ) & 
% 1.65/1.83                   ( ( k2_relset_1 @
% 1.65/1.83                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.65/1.83                       ( k2_tops_2 @
% 1.65/1.83                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.65/1.83                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.83    (~( ![A:$i]:
% 1.65/1.83        ( ( l1_struct_0 @ A ) =>
% 1.65/1.83          ( ![B:$i]:
% 1.65/1.83            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.65/1.83              ( ![C:$i]:
% 1.65/1.83                ( ( ( v1_funct_1 @ C ) & 
% 1.65/1.83                    ( v1_funct_2 @
% 1.65/1.83                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.83                    ( m1_subset_1 @
% 1.65/1.83                      C @ 
% 1.65/1.83                      ( k1_zfmisc_1 @
% 1.65/1.83                        ( k2_zfmisc_1 @
% 1.65/1.83                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.83                  ( ( ( ( k2_relset_1 @
% 1.65/1.83                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.65/1.83                        ( k2_struct_0 @ B ) ) & 
% 1.65/1.83                      ( v2_funct_1 @ C ) ) =>
% 1.65/1.83                    ( ( ( k1_relset_1 @
% 1.65/1.83                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.65/1.83                          ( k2_tops_2 @
% 1.65/1.83                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.65/1.83                        ( k2_struct_0 @ B ) ) & 
% 1.65/1.83                      ( ( k2_relset_1 @
% 1.65/1.83                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.65/1.83                          ( k2_tops_2 @
% 1.65/1.83                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.65/1.83                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.65/1.83    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.65/1.83  thf('3', plain,
% 1.65/1.83      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83          != (k2_struct_0 @ sk_B))
% 1.65/1.83        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83            != (k2_struct_0 @ sk_A)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('4', plain,
% 1.65/1.83      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83          != (k2_struct_0 @ sk_A)))
% 1.65/1.83         <= (~
% 1.65/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83                = (k2_struct_0 @ sk_A))))),
% 1.65/1.83      inference('split', [status(esa)], ['3'])).
% 1.65/1.83  thf('5', plain,
% 1.65/1.83      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83           != (k2_struct_0 @ sk_A))
% 1.65/1.83         | ~ (l1_struct_0 @ sk_B)))
% 1.65/1.83         <= (~
% 1.65/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83                = (k2_struct_0 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['2', '4'])).
% 1.65/1.83  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('7', plain,
% 1.65/1.83      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83          != (k2_struct_0 @ sk_A)))
% 1.65/1.83         <= (~
% 1.65/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83                = (k2_struct_0 @ sk_A))))),
% 1.65/1.83      inference('demod', [status(thm)], ['5', '6'])).
% 1.65/1.83  thf('8', plain,
% 1.65/1.83      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83           != (k2_struct_0 @ sk_A))
% 1.65/1.83         | ~ (l1_struct_0 @ sk_B)))
% 1.65/1.83         <= (~
% 1.65/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83                = (k2_struct_0 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['1', '7'])).
% 1.65/1.83  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('10', plain,
% 1.65/1.83      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83          != (k2_struct_0 @ sk_A)))
% 1.65/1.83         <= (~
% 1.65/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.83                = (k2_struct_0 @ sk_A))))),
% 1.65/1.83      inference('demod', [status(thm)], ['8', '9'])).
% 1.65/1.83  thf('11', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C @ 
% 1.65/1.83        (k1_zfmisc_1 @ 
% 1.65/1.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(redefinition_k2_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.65/1.83  thf('12', plain,
% 1.65/1.83      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.65/1.83         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 1.65/1.83          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.83  thf('13', plain,
% 1.65/1.83      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.65/1.83         = (k2_relat_1 @ sk_C))),
% 1.65/1.83      inference('sup-', [status(thm)], ['11', '12'])).
% 1.65/1.83  thf('14', plain,
% 1.65/1.83      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.65/1.83         = (k2_struct_0 @ sk_B))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('16', plain,
% 1.65/1.83      (![X21 : $i]:
% 1.65/1.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.83  thf('17', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C @ 
% 1.65/1.83        (k1_zfmisc_1 @ 
% 1.65/1.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('18', plain,
% 1.65/1.83      (((m1_subset_1 @ sk_C @ 
% 1.65/1.83         (k1_zfmisc_1 @ 
% 1.65/1.83          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.65/1.83        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup+', [status(thm)], ['16', '17'])).
% 1.65/1.83  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('20', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C @ 
% 1.65/1.83        (k1_zfmisc_1 @ 
% 1.65/1.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.65/1.83      inference('demod', [status(thm)], ['18', '19'])).
% 1.65/1.83  thf(cc5_funct_2, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.65/1.83       ( ![C:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.65/1.83             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.65/1.83  thf('21', plain,
% 1.65/1.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.65/1.83          | (v1_partfun1 @ X13 @ X14)
% 1.65/1.83          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 1.65/1.83          | ~ (v1_funct_1 @ X13)
% 1.65/1.83          | (v1_xboole_0 @ X15))),
% 1.65/1.83      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.65/1.83  thf('22', plain,
% 1.65/1.83      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.65/1.83        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.83        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.65/1.83        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['20', '21'])).
% 1.65/1.83  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('24', plain,
% 1.65/1.83      (![X21 : $i]:
% 1.65/1.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.83  thf('25', plain,
% 1.65/1.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('26', plain,
% 1.65/1.83      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.65/1.83        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup+', [status(thm)], ['24', '25'])).
% 1.65/1.83  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('28', plain,
% 1.65/1.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.65/1.83      inference('demod', [status(thm)], ['26', '27'])).
% 1.65/1.83  thf('29', plain,
% 1.65/1.83      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.65/1.83        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('demod', [status(thm)], ['22', '23', '28'])).
% 1.65/1.83  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('31', plain,
% 1.65/1.83      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.65/1.83        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('demod', [status(thm)], ['29', '30'])).
% 1.65/1.83  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('33', plain,
% 1.65/1.83      (![X21 : $i]:
% 1.65/1.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.83  thf(fc2_struct_0, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.65/1.83       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.65/1.83  thf('34', plain,
% 1.65/1.83      (![X22 : $i]:
% 1.65/1.83         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 1.65/1.83          | ~ (l1_struct_0 @ X22)
% 1.65/1.83          | (v2_struct_0 @ X22))),
% 1.65/1.83      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.65/1.83  thf('35', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.65/1.83          | ~ (l1_struct_0 @ X0)
% 1.65/1.83          | (v2_struct_0 @ X0)
% 1.65/1.83          | ~ (l1_struct_0 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['33', '34'])).
% 1.65/1.83  thf('36', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((v2_struct_0 @ X0)
% 1.65/1.83          | ~ (l1_struct_0 @ X0)
% 1.65/1.83          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.65/1.83      inference('simplify', [status(thm)], ['35'])).
% 1.65/1.83  thf('37', plain,
% 1.65/1.83      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.65/1.83        | ~ (l1_struct_0 @ sk_B)
% 1.65/1.83        | (v2_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup-', [status(thm)], ['32', '36'])).
% 1.65/1.83  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('39', plain,
% 1.65/1.83      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.65/1.83      inference('demod', [status(thm)], ['37', '38'])).
% 1.65/1.83  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('41', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.65/1.83      inference('clc', [status(thm)], ['39', '40'])).
% 1.65/1.83  thf('42', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('clc', [status(thm)], ['31', '41'])).
% 1.65/1.83  thf(d4_partfun1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.65/1.83       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.65/1.83  thf('43', plain,
% 1.65/1.83      (![X16 : $i, X17 : $i]:
% 1.65/1.83         (~ (v1_partfun1 @ X17 @ X16)
% 1.65/1.83          | ((k1_relat_1 @ X17) = (X16))
% 1.65/1.83          | ~ (v4_relat_1 @ X17 @ X16)
% 1.65/1.83          | ~ (v1_relat_1 @ X17))),
% 1.65/1.83      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.65/1.83  thf('44', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.83        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.65/1.83        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['42', '43'])).
% 1.65/1.83  thf('45', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C @ 
% 1.65/1.83        (k1_zfmisc_1 @ 
% 1.65/1.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(cc1_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( v1_relat_1 @ C ) ))).
% 1.65/1.83  thf('46', plain,
% 1.65/1.83      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((v1_relat_1 @ X1)
% 1.65/1.83          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 1.65/1.83      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.83  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.83      inference('sup-', [status(thm)], ['45', '46'])).
% 1.65/1.83  thf('48', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C @ 
% 1.65/1.83        (k1_zfmisc_1 @ 
% 1.65/1.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(cc2_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.65/1.83  thf('49', plain,
% 1.65/1.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.65/1.83         ((v4_relat_1 @ X4 @ X5)
% 1.65/1.83          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.65/1.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.83  thf('50', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['48', '49'])).
% 1.65/1.83  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.65/1.83  thf('52', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.65/1.83  thf('53', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('54', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C @ 
% 1.65/1.83        (k1_zfmisc_1 @ 
% 1.65/1.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.65/1.83      inference('demod', [status(thm)], ['18', '19'])).
% 1.65/1.83  thf('55', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('56', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C @ 
% 1.65/1.83        (k1_zfmisc_1 @ 
% 1.65/1.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.65/1.83      inference('demod', [status(thm)], ['54', '55'])).
% 1.65/1.83  thf('57', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.65/1.83  thf('58', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C @ 
% 1.65/1.83        (k1_zfmisc_1 @ 
% 1.65/1.83         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.65/1.83      inference('demod', [status(thm)], ['56', '57'])).
% 1.65/1.83  thf(d4_tops_2, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.83       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.65/1.83         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.65/1.83  thf('59', plain,
% 1.65/1.83      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.65/1.83         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 1.65/1.83          | ~ (v2_funct_1 @ X25)
% 1.65/1.83          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 1.65/1.83          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.65/1.83          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 1.65/1.83          | ~ (v1_funct_1 @ X25))),
% 1.65/1.83      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.65/1.83  thf('60', plain,
% 1.65/1.83      ((~ (v1_funct_1 @ sk_C)
% 1.65/1.83        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.65/1.83        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.83            = (k2_funct_1 @ sk_C))
% 1.65/1.83        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.83        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.83            != (k2_relat_1 @ sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['58', '59'])).
% 1.65/1.83  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('62', plain,
% 1.65/1.83      (![X21 : $i]:
% 1.65/1.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.83  thf('63', plain,
% 1.65/1.83      (![X21 : $i]:
% 1.65/1.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.83  thf('64', plain,
% 1.65/1.83      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('65', plain,
% 1.65/1.83      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.65/1.83        | ~ (l1_struct_0 @ sk_A))),
% 1.65/1.83      inference('sup+', [status(thm)], ['63', '64'])).
% 1.65/1.83  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('67', plain,
% 1.65/1.83      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.65/1.83      inference('demod', [status(thm)], ['65', '66'])).
% 1.65/1.83  thf('68', plain,
% 1.65/1.83      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.65/1.83        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup+', [status(thm)], ['62', '67'])).
% 1.65/1.83  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('70', plain,
% 1.65/1.83      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.65/1.83      inference('demod', [status(thm)], ['68', '69'])).
% 1.65/1.83  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('72', plain,
% 1.65/1.83      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.65/1.83      inference('demod', [status(thm)], ['70', '71'])).
% 1.65/1.83  thf('73', plain,
% 1.65/1.83      (![X21 : $i]:
% 1.65/1.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.83  thf('74', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('clc', [status(thm)], ['31', '41'])).
% 1.65/1.83  thf('75', plain,
% 1.65/1.83      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.65/1.83      inference('sup+', [status(thm)], ['73', '74'])).
% 1.65/1.83  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('77', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['75', '76'])).
% 1.65/1.83  thf('78', plain,
% 1.65/1.83      (![X16 : $i, X17 : $i]:
% 1.65/1.83         (~ (v1_partfun1 @ X17 @ X16)
% 1.65/1.83          | ((k1_relat_1 @ X17) = (X16))
% 1.65/1.83          | ~ (v4_relat_1 @ X17 @ X16)
% 1.65/1.83          | ~ (v1_relat_1 @ X17))),
% 1.65/1.83      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.65/1.83  thf('79', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.83        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.65/1.83        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['77', '78'])).
% 1.65/1.83  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.83      inference('sup-', [status(thm)], ['45', '46'])).
% 1.65/1.83  thf('81', plain,
% 1.65/1.83      (![X21 : $i]:
% 1.65/1.83         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.83  thf('82', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_C @ 
% 1.65/1.83        (k1_zfmisc_1 @ 
% 1.65/1.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('83', plain,
% 1.65/1.83      (((m1_subset_1 @ sk_C @ 
% 1.65/1.83         (k1_zfmisc_1 @ 
% 1.65/1.83          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.65/1.84        | ~ (l1_struct_0 @ sk_A))),
% 1.65/1.84      inference('sup+', [status(thm)], ['81', '82'])).
% 1.65/1.84  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('85', plain,
% 1.65/1.84      ((m1_subset_1 @ sk_C @ 
% 1.65/1.84        (k1_zfmisc_1 @ 
% 1.65/1.84         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.84      inference('demod', [status(thm)], ['83', '84'])).
% 1.65/1.84  thf('86', plain,
% 1.65/1.84      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.65/1.84         ((v4_relat_1 @ X4 @ X5)
% 1.65/1.84          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.65/1.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.84  thf('87', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.65/1.84      inference('sup-', [status(thm)], ['85', '86'])).
% 1.65/1.84  thf('88', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.65/1.84      inference('demod', [status(thm)], ['79', '80', '87'])).
% 1.65/1.84  thf('89', plain,
% 1.65/1.84      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['72', '88'])).
% 1.65/1.84  thf('90', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('91', plain,
% 1.65/1.84      (![X21 : $i]:
% 1.65/1.84         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.84  thf('92', plain,
% 1.65/1.84      (![X21 : $i]:
% 1.65/1.84         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.84  thf('93', plain,
% 1.65/1.84      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.65/1.84         = (k2_struct_0 @ sk_B))),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('94', plain,
% 1.65/1.84      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.65/1.84          = (k2_struct_0 @ sk_B))
% 1.65/1.84        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.84      inference('sup+', [status(thm)], ['92', '93'])).
% 1.65/1.84  thf('95', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('96', plain,
% 1.65/1.84      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.65/1.84         = (k2_struct_0 @ sk_B))),
% 1.65/1.84      inference('demod', [status(thm)], ['94', '95'])).
% 1.65/1.84  thf('97', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.84      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.84  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.84      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.84  thf('99', plain,
% 1.65/1.84      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.84         = (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['96', '97', '98'])).
% 1.65/1.84  thf('100', plain,
% 1.65/1.84      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.84          = (k2_relat_1 @ sk_C))
% 1.65/1.84        | ~ (l1_struct_0 @ sk_A))),
% 1.65/1.84      inference('sup+', [status(thm)], ['91', '99'])).
% 1.65/1.84  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('102', plain,
% 1.65/1.84      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.84         = (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['100', '101'])).
% 1.65/1.84  thf('103', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.65/1.84      inference('demod', [status(thm)], ['79', '80', '87'])).
% 1.65/1.84  thf('104', plain,
% 1.65/1.84      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.84         = (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['102', '103'])).
% 1.65/1.84  thf('105', plain,
% 1.65/1.84      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.84          = (k2_funct_1 @ sk_C))
% 1.65/1.84        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.65/1.84      inference('demod', [status(thm)], ['60', '61', '89', '90', '104'])).
% 1.65/1.84  thf('106', plain,
% 1.65/1.84      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.84         = (k2_funct_1 @ sk_C))),
% 1.65/1.84      inference('simplify', [status(thm)], ['105'])).
% 1.65/1.84  thf('107', plain,
% 1.65/1.84      ((m1_subset_1 @ sk_C @ 
% 1.65/1.84        (k1_zfmisc_1 @ 
% 1.65/1.84         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.65/1.84      inference('demod', [status(thm)], ['56', '57'])).
% 1.65/1.84  thf(t31_funct_2, axiom,
% 1.65/1.84    (![A:$i,B:$i,C:$i]:
% 1.65/1.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.84       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.65/1.84         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.65/1.84           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.65/1.84           ( m1_subset_1 @
% 1.65/1.84             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.65/1.84  thf('108', plain,
% 1.65/1.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.65/1.84         (~ (v2_funct_1 @ X18)
% 1.65/1.84          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 1.65/1.84          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 1.65/1.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.65/1.84          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 1.65/1.84          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 1.65/1.84          | ~ (v1_funct_1 @ X18))),
% 1.65/1.84      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.65/1.84  thf('109', plain,
% 1.65/1.84      ((~ (v1_funct_1 @ sk_C)
% 1.65/1.84        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.65/1.84        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.84           (k1_zfmisc_1 @ 
% 1.65/1.84            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.65/1.84        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.84            != (k2_relat_1 @ sk_C))
% 1.65/1.84        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.84      inference('sup-', [status(thm)], ['107', '108'])).
% 1.65/1.84  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('111', plain,
% 1.65/1.84      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['72', '88'])).
% 1.65/1.84  thf('112', plain,
% 1.65/1.84      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.84         = (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['102', '103'])).
% 1.65/1.84  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('114', plain,
% 1.65/1.84      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.84         (k1_zfmisc_1 @ 
% 1.65/1.84          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.65/1.84        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.65/1.84      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 1.65/1.84  thf('115', plain,
% 1.65/1.84      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.84        (k1_zfmisc_1 @ 
% 1.65/1.84         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.65/1.84      inference('simplify', [status(thm)], ['114'])).
% 1.65/1.84  thf('116', plain,
% 1.65/1.84      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.65/1.84         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 1.65/1.84          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.65/1.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.84  thf('117', plain,
% 1.65/1.84      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.84         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['115', '116'])).
% 1.65/1.84  thf('118', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.65/1.84      inference('demod', [status(thm)], ['79', '80', '87'])).
% 1.65/1.84  thf('119', plain,
% 1.65/1.84      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_A))))),
% 1.65/1.84      inference('demod', [status(thm)],
% 1.65/1.84                ['10', '15', '51', '52', '53', '106', '117', '118'])).
% 1.65/1.84  thf('120', plain,
% 1.65/1.84      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.84        (k1_zfmisc_1 @ 
% 1.65/1.84         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.65/1.84      inference('simplify', [status(thm)], ['114'])).
% 1.65/1.84  thf(redefinition_k1_relset_1, axiom,
% 1.65/1.84    (![A:$i,B:$i,C:$i]:
% 1.65/1.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.65/1.84  thf('121', plain,
% 1.65/1.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.65/1.84         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 1.65/1.84          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.65/1.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.65/1.84  thf('122', plain,
% 1.65/1.84      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.84         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['120', '121'])).
% 1.65/1.84  thf('123', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v2_funct_1 @ X0)
% 1.65/1.84          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.84          | ~ (v1_funct_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.84  thf('124', plain,
% 1.65/1.84      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.84        (k1_zfmisc_1 @ 
% 1.65/1.84         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.65/1.84      inference('simplify', [status(thm)], ['114'])).
% 1.65/1.84  thf('125', plain,
% 1.65/1.84      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.65/1.84         ((v4_relat_1 @ X4 @ X5)
% 1.65/1.84          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.65/1.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.84  thf('126', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('sup-', [status(thm)], ['124', '125'])).
% 1.65/1.84  thf('127', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v2_funct_1 @ X0)
% 1.65/1.84          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.84          | ~ (v1_funct_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.84  thf('128', plain,
% 1.65/1.84      (![X16 : $i, X17 : $i]:
% 1.65/1.84         (((k1_relat_1 @ X17) != (X16))
% 1.65/1.84          | (v1_partfun1 @ X17 @ X16)
% 1.65/1.84          | ~ (v4_relat_1 @ X17 @ X16)
% 1.65/1.84          | ~ (v1_relat_1 @ X17))),
% 1.65/1.84      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.65/1.84  thf('129', plain,
% 1.65/1.84      (![X17 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X17)
% 1.65/1.84          | ~ (v4_relat_1 @ X17 @ (k1_relat_1 @ X17))
% 1.65/1.84          | (v1_partfun1 @ X17 @ (k1_relat_1 @ X17)))),
% 1.65/1.84      inference('simplify', [status(thm)], ['128'])).
% 1.65/1.84  thf('130', plain,
% 1.65/1.84      (![X0 : $i]:
% 1.65/1.84         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_funct_1 @ X0)
% 1.65/1.84          | ~ (v2_funct_1 @ X0)
% 1.65/1.84          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.84          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['127', '129'])).
% 1.65/1.84  thf('131', plain,
% 1.65/1.84      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.84        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.84           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.65/1.84        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.84        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.84        | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.84      inference('sup-', [status(thm)], ['126', '130'])).
% 1.65/1.84  thf('132', plain,
% 1.65/1.84      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.84        (k1_zfmisc_1 @ 
% 1.65/1.84         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.65/1.84      inference('simplify', [status(thm)], ['114'])).
% 1.65/1.84  thf('133', plain,
% 1.65/1.84      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.84         ((v1_relat_1 @ X1)
% 1.65/1.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 1.65/1.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.84  thf('134', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.65/1.84      inference('sup-', [status(thm)], ['132', '133'])).
% 1.65/1.84  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.84      inference('sup-', [status(thm)], ['45', '46'])).
% 1.65/1.84  thf('138', plain,
% 1.65/1.84      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.84      inference('demod', [status(thm)], ['131', '134', '135', '136', '137'])).
% 1.65/1.84  thf('139', plain,
% 1.65/1.84      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.65/1.84        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.84        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.84        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.84      inference('sup+', [status(thm)], ['123', '138'])).
% 1.65/1.84  thf('140', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.84      inference('sup-', [status(thm)], ['45', '46'])).
% 1.65/1.84  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('143', plain,
% 1.65/1.84      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 1.65/1.84  thf('144', plain,
% 1.65/1.84      (![X16 : $i, X17 : $i]:
% 1.65/1.84         (~ (v1_partfun1 @ X17 @ X16)
% 1.65/1.84          | ((k1_relat_1 @ X17) = (X16))
% 1.65/1.84          | ~ (v4_relat_1 @ X17 @ X16)
% 1.65/1.84          | ~ (v1_relat_1 @ X17))),
% 1.65/1.84      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.65/1.84  thf('145', plain,
% 1.65/1.84      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.84        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.65/1.84        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['143', '144'])).
% 1.65/1.84  thf('146', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.65/1.84      inference('sup-', [status(thm)], ['132', '133'])).
% 1.65/1.84  thf('147', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('sup-', [status(thm)], ['124', '125'])).
% 1.65/1.84  thf('148', plain,
% 1.65/1.84      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['145', '146', '147'])).
% 1.65/1.84  thf('149', plain,
% 1.65/1.84      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.84         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['122', '148'])).
% 1.65/1.84  thf('150', plain,
% 1.65/1.84      (![X21 : $i]:
% 1.65/1.84         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.84  thf('151', plain,
% 1.65/1.84      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.84         = (k2_funct_1 @ sk_C))),
% 1.65/1.84      inference('simplify', [status(thm)], ['105'])).
% 1.65/1.84  thf('152', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.84      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.84  thf('153', plain,
% 1.65/1.84      (![X21 : $i]:
% 1.65/1.84         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.65/1.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.84  thf('154', plain,
% 1.65/1.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84          != (k2_struct_0 @ sk_B)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('split', [status(esa)], ['3'])).
% 1.65/1.84  thf('155', plain,
% 1.65/1.84      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84           != (k2_struct_0 @ sk_B))
% 1.65/1.84         | ~ (l1_struct_0 @ sk_B)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('sup-', [status(thm)], ['153', '154'])).
% 1.65/1.84  thf('156', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('157', plain,
% 1.65/1.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84          != (k2_struct_0 @ sk_B)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('demod', [status(thm)], ['155', '156'])).
% 1.65/1.84  thf('158', plain,
% 1.65/1.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.65/1.84          != (k2_struct_0 @ sk_B)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('sup-', [status(thm)], ['152', '157'])).
% 1.65/1.84  thf('159', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.84      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.84  thf('160', plain,
% 1.65/1.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.65/1.84          != (k2_relat_1 @ sk_C)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('demod', [status(thm)], ['158', '159'])).
% 1.65/1.84  thf('161', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.65/1.84      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.65/1.84  thf('162', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.65/1.84      inference('demod', [status(thm)], ['44', '47', '50'])).
% 1.65/1.84  thf('163', plain,
% 1.65/1.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.84          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.65/1.84          != (k2_relat_1 @ sk_C)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('demod', [status(thm)], ['160', '161', '162'])).
% 1.65/1.84  thf('164', plain,
% 1.65/1.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.84          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('sup-', [status(thm)], ['151', '163'])).
% 1.65/1.84  thf('165', plain,
% 1.65/1.84      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.84           (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 1.65/1.84         | ~ (l1_struct_0 @ sk_B)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('sup-', [status(thm)], ['150', '164'])).
% 1.65/1.84  thf('166', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.84      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.84  thf('167', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('168', plain,
% 1.65/1.84      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.84          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('demod', [status(thm)], ['165', '166', '167'])).
% 1.65/1.84  thf('169', plain,
% 1.65/1.84      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.65/1.84         <= (~
% 1.65/1.84             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84                = (k2_struct_0 @ sk_B))))),
% 1.65/1.84      inference('sup-', [status(thm)], ['149', '168'])).
% 1.65/1.84  thf('170', plain,
% 1.65/1.84      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84          = (k2_struct_0 @ sk_B)))),
% 1.65/1.84      inference('simplify', [status(thm)], ['169'])).
% 1.65/1.84  thf('171', plain,
% 1.65/1.84      (~
% 1.65/1.84       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84          = (k2_struct_0 @ sk_A))) | 
% 1.65/1.84       ~
% 1.65/1.84       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84          = (k2_struct_0 @ sk_B)))),
% 1.65/1.84      inference('split', [status(esa)], ['3'])).
% 1.65/1.84  thf('172', plain,
% 1.65/1.84      (~
% 1.65/1.84       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.84          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.84          = (k2_struct_0 @ sk_A)))),
% 1.65/1.84      inference('sat_resolution*', [status(thm)], ['170', '171'])).
% 1.65/1.84  thf('173', plain,
% 1.65/1.84      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.65/1.84      inference('simpl_trail', [status(thm)], ['119', '172'])).
% 1.65/1.84  thf('174', plain,
% 1.65/1.84      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.65/1.84        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.84        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.84        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.84      inference('sup-', [status(thm)], ['0', '173'])).
% 1.65/1.84  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.84      inference('sup-', [status(thm)], ['45', '46'])).
% 1.65/1.84  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('177', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('178', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 1.65/1.84      inference('demod', [status(thm)], ['174', '175', '176', '177'])).
% 1.65/1.84  thf('179', plain, ($false), inference('simplify', [status(thm)], ['178'])).
% 1.65/1.84  
% 1.65/1.84  % SZS output end Refutation
% 1.65/1.84  
% 1.65/1.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
