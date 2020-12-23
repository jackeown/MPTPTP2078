%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xI5FXuljGm

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:50 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  213 (3448 expanded)
%              Number of leaves         :   36 (1003 expanded)
%              Depth                    :   30
%              Number of atoms          : 1929 (89389 expanded)
%              Number of equality atoms :  123 (4512 expanded)
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

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','38'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('43',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','44','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','44','47'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','44','47'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

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

thf('56',plain,(
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

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','38'])).

thf('72',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('78',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','84'])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','85'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('89',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('96',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['88','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','84'])).

thf('101',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','86','87','101'])).

thf('103',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

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

thf('105',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','85'])).

thf('109',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('114',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','84'])).

thf('116',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','48','49','50','103','114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('118',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('119',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('122',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('123',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('125',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != X16 )
      | ( v1_partfun1 @ X17 @ X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('126',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v4_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
      | ( v1_partfun1 @ X17 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','126'])).

thf('128',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','127'])).

thf('129',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('130',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('131',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('135',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['128','131','132','133','134'])).

thf('136',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['120','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('144',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('145',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','145'])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('148',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('149',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('150',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('151',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','156'])).

thf('158',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('160',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','44','47'])).

thf('162',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','44','47'])).

thf('163',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['102'])).

thf('164',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','164'])).

thf('166',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('168',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['166','167'])).

thf('169',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['116','168'])).

thf('170',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['170','171','172','173'])).

thf('175',plain,(
    $false ),
    inference(simplify,[status(thm)],['174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xI5FXuljGm
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.20/1.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.20/1.41  % Solved by: fo/fo7.sh
% 1.20/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.41  % done 295 iterations in 0.989s
% 1.20/1.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.20/1.41  % SZS output start Refutation
% 1.20/1.41  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.20/1.41  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.20/1.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.20/1.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.41  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.20/1.41  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.20/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.41  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.41  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.20/1.41  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.20/1.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.41  thf(sk_C_type, type, sk_C: $i).
% 1.20/1.41  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.20/1.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.20/1.41  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.20/1.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.20/1.41  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.20/1.41  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.20/1.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.20/1.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.41  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.20/1.41  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.20/1.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.20/1.41  thf(t55_funct_1, axiom,
% 1.20/1.41    (![A:$i]:
% 1.20/1.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.41       ( ( v2_funct_1 @ A ) =>
% 1.20/1.41         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.20/1.41           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.20/1.41  thf('0', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v2_funct_1 @ X0)
% 1.20/1.41          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.41          | ~ (v1_funct_1 @ X0)
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.41  thf(d3_struct_0, axiom,
% 1.20/1.41    (![A:$i]:
% 1.20/1.41     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.20/1.41  thf('1', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('2', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf(t62_tops_2, conjecture,
% 1.20/1.41    (![A:$i]:
% 1.20/1.41     ( ( l1_struct_0 @ A ) =>
% 1.20/1.41       ( ![B:$i]:
% 1.20/1.41         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.20/1.41           ( ![C:$i]:
% 1.20/1.41             ( ( ( v1_funct_1 @ C ) & 
% 1.20/1.41                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.20/1.41                 ( m1_subset_1 @
% 1.20/1.41                   C @ 
% 1.20/1.41                   ( k1_zfmisc_1 @
% 1.20/1.41                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.20/1.41               ( ( ( ( k2_relset_1 @
% 1.20/1.41                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.20/1.41                     ( k2_struct_0 @ B ) ) & 
% 1.20/1.41                   ( v2_funct_1 @ C ) ) =>
% 1.20/1.41                 ( ( ( k1_relset_1 @
% 1.20/1.41                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.20/1.41                       ( k2_tops_2 @
% 1.20/1.41                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.20/1.41                     ( k2_struct_0 @ B ) ) & 
% 1.20/1.41                   ( ( k2_relset_1 @
% 1.20/1.41                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.20/1.41                       ( k2_tops_2 @
% 1.20/1.41                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.20/1.41                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.20/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.41    (~( ![A:$i]:
% 1.20/1.41        ( ( l1_struct_0 @ A ) =>
% 1.20/1.41          ( ![B:$i]:
% 1.20/1.41            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.20/1.41              ( ![C:$i]:
% 1.20/1.41                ( ( ( v1_funct_1 @ C ) & 
% 1.20/1.41                    ( v1_funct_2 @
% 1.20/1.41                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.20/1.41                    ( m1_subset_1 @
% 1.20/1.41                      C @ 
% 1.20/1.41                      ( k1_zfmisc_1 @
% 1.20/1.41                        ( k2_zfmisc_1 @
% 1.20/1.41                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.20/1.41                  ( ( ( ( k2_relset_1 @
% 1.20/1.41                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.20/1.41                        ( k2_struct_0 @ B ) ) & 
% 1.20/1.41                      ( v2_funct_1 @ C ) ) =>
% 1.20/1.41                    ( ( ( k1_relset_1 @
% 1.20/1.41                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.20/1.41                          ( k2_tops_2 @
% 1.20/1.41                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.20/1.41                        ( k2_struct_0 @ B ) ) & 
% 1.20/1.41                      ( ( k2_relset_1 @
% 1.20/1.41                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.20/1.41                          ( k2_tops_2 @
% 1.20/1.41                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.20/1.41                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.20/1.41    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.20/1.41  thf('3', plain,
% 1.20/1.41      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          != (k2_struct_0 @ sk_B))
% 1.20/1.41        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41            != (k2_struct_0 @ sk_A)))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('4', plain,
% 1.20/1.41      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          != (k2_struct_0 @ sk_A)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_A))))),
% 1.20/1.41      inference('split', [status(esa)], ['3'])).
% 1.20/1.41  thf('5', plain,
% 1.20/1.41      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41           != (k2_struct_0 @ sk_A))
% 1.20/1.41         | ~ (l1_struct_0 @ sk_B)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_A))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['2', '4'])).
% 1.20/1.41  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('7', plain,
% 1.20/1.41      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          != (k2_struct_0 @ sk_A)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_A))))),
% 1.20/1.41      inference('demod', [status(thm)], ['5', '6'])).
% 1.20/1.41  thf('8', plain,
% 1.20/1.41      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41           != (k2_struct_0 @ sk_A))
% 1.20/1.41         | ~ (l1_struct_0 @ sk_B)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_A))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['1', '7'])).
% 1.20/1.41  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('10', plain,
% 1.20/1.41      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          != (k2_struct_0 @ sk_A)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_A))))),
% 1.20/1.41      inference('demod', [status(thm)], ['8', '9'])).
% 1.20/1.41  thf('11', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf(redefinition_k2_relset_1, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.41       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.20/1.41  thf('12', plain,
% 1.20/1.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.20/1.41         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 1.20/1.41          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.20/1.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.20/1.41  thf('13', plain,
% 1.20/1.41      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.20/1.41         = (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('sup-', [status(thm)], ['11', '12'])).
% 1.20/1.41  thf('14', plain,
% 1.20/1.41      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.20/1.41         = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('16', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('17', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('18', plain,
% 1.20/1.41      (((m1_subset_1 @ sk_C @ 
% 1.20/1.41         (k1_zfmisc_1 @ 
% 1.20/1.41          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.20/1.41        | ~ (l1_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['16', '17'])).
% 1.20/1.41  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('20', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('demod', [status(thm)], ['18', '19'])).
% 1.20/1.41  thf(cc5_funct_2, axiom,
% 1.20/1.41    (![A:$i,B:$i]:
% 1.20/1.41     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.20/1.41       ( ![C:$i]:
% 1.20/1.41         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.41           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.20/1.41             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.20/1.41  thf('21', plain,
% 1.20/1.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.20/1.41         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.20/1.41          | (v1_partfun1 @ X13 @ X14)
% 1.20/1.41          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 1.20/1.41          | ~ (v1_funct_1 @ X13)
% 1.20/1.41          | (v1_xboole_0 @ X15))),
% 1.20/1.41      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.20/1.41  thf('22', plain,
% 1.20/1.41      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.20/1.41        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.41        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.20/1.41        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['20', '21'])).
% 1.20/1.41  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('24', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('25', plain,
% 1.20/1.41      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('26', plain,
% 1.20/1.41      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.20/1.41        | ~ (l1_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['24', '25'])).
% 1.20/1.41  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('28', plain,
% 1.20/1.41      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('demod', [status(thm)], ['26', '27'])).
% 1.20/1.41  thf('29', plain,
% 1.20/1.41      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.20/1.41        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.20/1.41      inference('demod', [status(thm)], ['22', '23', '28'])).
% 1.20/1.41  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('31', plain,
% 1.20/1.41      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.20/1.41        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.20/1.41      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.41  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf(fc5_struct_0, axiom,
% 1.20/1.41    (![A:$i]:
% 1.20/1.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.20/1.41       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.20/1.41  thf('33', plain,
% 1.20/1.41      (![X22 : $i]:
% 1.20/1.41         (~ (v1_xboole_0 @ (k2_struct_0 @ X22))
% 1.20/1.41          | ~ (l1_struct_0 @ X22)
% 1.20/1.41          | (v2_struct_0 @ X22))),
% 1.20/1.41      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.20/1.41  thf('34', plain,
% 1.20/1.41      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.20/1.41        | (v2_struct_0 @ sk_B)
% 1.20/1.41        | ~ (l1_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup-', [status(thm)], ['32', '33'])).
% 1.20/1.41  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('36', plain,
% 1.20/1.41      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.20/1.41      inference('demod', [status(thm)], ['34', '35'])).
% 1.20/1.41  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('38', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('clc', [status(thm)], ['36', '37'])).
% 1.20/1.41  thf('39', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('clc', [status(thm)], ['31', '38'])).
% 1.20/1.41  thf(d4_partfun1, axiom,
% 1.20/1.41    (![A:$i,B:$i]:
% 1.20/1.41     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.20/1.41       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.20/1.41  thf('40', plain,
% 1.20/1.41      (![X16 : $i, X17 : $i]:
% 1.20/1.41         (~ (v1_partfun1 @ X17 @ X16)
% 1.20/1.41          | ((k1_relat_1 @ X17) = (X16))
% 1.20/1.41          | ~ (v4_relat_1 @ X17 @ X16)
% 1.20/1.41          | ~ (v1_relat_1 @ X17))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.20/1.41  thf('41', plain,
% 1.20/1.41      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.41        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.20/1.41        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['39', '40'])).
% 1.20/1.41  thf('42', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf(cc1_relset_1, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.41       ( v1_relat_1 @ C ) ))).
% 1.20/1.41  thf('43', plain,
% 1.20/1.41      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.41         ((v1_relat_1 @ X1)
% 1.20/1.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 1.20/1.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.41  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.41      inference('sup-', [status(thm)], ['42', '43'])).
% 1.20/1.41  thf('45', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf(cc2_relset_1, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.41       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.20/1.41  thf('46', plain,
% 1.20/1.41      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.20/1.41         ((v4_relat_1 @ X4 @ X5)
% 1.20/1.41          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.20/1.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.41  thf('47', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('sup-', [status(thm)], ['45', '46'])).
% 1.20/1.41  thf('48', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('demod', [status(thm)], ['41', '44', '47'])).
% 1.20/1.41  thf('49', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('demod', [status(thm)], ['41', '44', '47'])).
% 1.20/1.41  thf('50', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('51', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('demod', [status(thm)], ['18', '19'])).
% 1.20/1.41  thf('52', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('53', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.20/1.41      inference('demod', [status(thm)], ['51', '52'])).
% 1.20/1.41  thf('54', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('demod', [status(thm)], ['41', '44', '47'])).
% 1.20/1.41  thf('55', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.20/1.41      inference('demod', [status(thm)], ['53', '54'])).
% 1.20/1.41  thf(d4_tops_2, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.41       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.20/1.41         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.20/1.41  thf('56', plain,
% 1.20/1.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.20/1.41         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 1.20/1.41          | ~ (v2_funct_1 @ X25)
% 1.20/1.41          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 1.20/1.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.20/1.41          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 1.20/1.41          | ~ (v1_funct_1 @ X25))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.20/1.41  thf('57', plain,
% 1.20/1.41      ((~ (v1_funct_1 @ sk_C)
% 1.20/1.41        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.20/1.41        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41            = (k2_funct_1 @ sk_C))
% 1.20/1.41        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.41        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41            != (k2_relat_1 @ sk_C)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['55', '56'])).
% 1.20/1.41  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('59', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('60', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('61', plain,
% 1.20/1.41      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('62', plain,
% 1.20/1.41      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.20/1.41        | ~ (l1_struct_0 @ sk_A))),
% 1.20/1.41      inference('sup+', [status(thm)], ['60', '61'])).
% 1.20/1.41  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('64', plain,
% 1.20/1.41      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.20/1.41      inference('demod', [status(thm)], ['62', '63'])).
% 1.20/1.41  thf('65', plain,
% 1.20/1.41      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.20/1.41        | ~ (l1_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['59', '64'])).
% 1.20/1.41  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('67', plain,
% 1.20/1.41      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('demod', [status(thm)], ['65', '66'])).
% 1.20/1.41  thf('68', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('69', plain,
% 1.20/1.41      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['67', '68'])).
% 1.20/1.41  thf('70', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('71', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('clc', [status(thm)], ['31', '38'])).
% 1.20/1.41  thf('72', plain,
% 1.20/1.41      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.20/1.41      inference('sup+', [status(thm)], ['70', '71'])).
% 1.20/1.41  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('74', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.20/1.41      inference('demod', [status(thm)], ['72', '73'])).
% 1.20/1.41  thf('75', plain,
% 1.20/1.41      (![X16 : $i, X17 : $i]:
% 1.20/1.41         (~ (v1_partfun1 @ X17 @ X16)
% 1.20/1.41          | ((k1_relat_1 @ X17) = (X16))
% 1.20/1.41          | ~ (v4_relat_1 @ X17 @ X16)
% 1.20/1.41          | ~ (v1_relat_1 @ X17))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.20/1.41  thf('76', plain,
% 1.20/1.41      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.41        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.20/1.41        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['74', '75'])).
% 1.20/1.41  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.41      inference('sup-', [status(thm)], ['42', '43'])).
% 1.20/1.41  thf('78', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('79', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('80', plain,
% 1.20/1.41      (((m1_subset_1 @ sk_C @ 
% 1.20/1.41         (k1_zfmisc_1 @ 
% 1.20/1.41          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.20/1.41        | ~ (l1_struct_0 @ sk_A))),
% 1.20/1.41      inference('sup+', [status(thm)], ['78', '79'])).
% 1.20/1.41  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('82', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.20/1.41      inference('demod', [status(thm)], ['80', '81'])).
% 1.20/1.41  thf('83', plain,
% 1.20/1.41      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.20/1.41         ((v4_relat_1 @ X4 @ X5)
% 1.20/1.41          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.20/1.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.41  thf('84', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.20/1.41      inference('sup-', [status(thm)], ['82', '83'])).
% 1.20/1.41  thf('85', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.20/1.41      inference('demod', [status(thm)], ['76', '77', '84'])).
% 1.20/1.41  thf('86', plain,
% 1.20/1.41      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['69', '85'])).
% 1.20/1.41  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('88', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('89', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('90', plain,
% 1.20/1.41      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.20/1.41         = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('91', plain,
% 1.20/1.41      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.20/1.41          = (k2_struct_0 @ sk_B))
% 1.20/1.41        | ~ (l1_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['89', '90'])).
% 1.20/1.41  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('93', plain,
% 1.20/1.41      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.20/1.41         = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('demod', [status(thm)], ['91', '92'])).
% 1.20/1.41  thf('94', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('95', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('96', plain,
% 1.20/1.41      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41         = (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.20/1.41  thf('97', plain,
% 1.20/1.41      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41          = (k2_relat_1 @ sk_C))
% 1.20/1.41        | ~ (l1_struct_0 @ sk_A))),
% 1.20/1.41      inference('sup+', [status(thm)], ['88', '96'])).
% 1.20/1.41  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('99', plain,
% 1.20/1.41      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41         = (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['97', '98'])).
% 1.20/1.41  thf('100', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.20/1.41      inference('demod', [status(thm)], ['76', '77', '84'])).
% 1.20/1.41  thf('101', plain,
% 1.20/1.41      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41         = (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['99', '100'])).
% 1.20/1.41  thf('102', plain,
% 1.20/1.41      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41          = (k2_funct_1 @ sk_C))
% 1.20/1.41        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.20/1.41      inference('demod', [status(thm)], ['57', '58', '86', '87', '101'])).
% 1.20/1.41  thf('103', plain,
% 1.20/1.41      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41         = (k2_funct_1 @ sk_C))),
% 1.20/1.41      inference('simplify', [status(thm)], ['102'])).
% 1.20/1.41  thf('104', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_C @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.20/1.41      inference('demod', [status(thm)], ['53', '54'])).
% 1.20/1.41  thf(t31_funct_2, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.41       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.20/1.41         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.20/1.41           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.20/1.41           ( m1_subset_1 @
% 1.20/1.41             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.20/1.41  thf('105', plain,
% 1.20/1.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.20/1.41         (~ (v2_funct_1 @ X18)
% 1.20/1.41          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 1.20/1.41          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 1.20/1.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.20/1.41          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 1.20/1.41          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 1.20/1.41          | ~ (v1_funct_1 @ X18))),
% 1.20/1.41      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.20/1.41  thf('106', plain,
% 1.20/1.41      ((~ (v1_funct_1 @ sk_C)
% 1.20/1.41        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.20/1.41        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.41           (k1_zfmisc_1 @ 
% 1.20/1.41            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.20/1.41        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41            != (k2_relat_1 @ sk_C))
% 1.20/1.41        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.41      inference('sup-', [status(thm)], ['104', '105'])).
% 1.20/1.41  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('108', plain,
% 1.20/1.41      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['69', '85'])).
% 1.20/1.41  thf('109', plain,
% 1.20/1.41      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41         = (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['99', '100'])).
% 1.20/1.41  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('111', plain,
% 1.20/1.41      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.41         (k1_zfmisc_1 @ 
% 1.20/1.41          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.20/1.41        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.20/1.41      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 1.20/1.41  thf('112', plain,
% 1.20/1.41      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.20/1.41      inference('simplify', [status(thm)], ['111'])).
% 1.20/1.41  thf('113', plain,
% 1.20/1.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.20/1.41         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 1.20/1.41          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.20/1.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.20/1.41  thf('114', plain,
% 1.20/1.41      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.20/1.41         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['112', '113'])).
% 1.20/1.41  thf('115', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.20/1.41      inference('demod', [status(thm)], ['76', '77', '84'])).
% 1.20/1.41  thf('116', plain,
% 1.20/1.41      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_A))))),
% 1.20/1.41      inference('demod', [status(thm)],
% 1.20/1.41                ['10', '15', '48', '49', '50', '103', '114', '115'])).
% 1.20/1.41  thf('117', plain,
% 1.20/1.41      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.20/1.41      inference('simplify', [status(thm)], ['111'])).
% 1.20/1.41  thf(redefinition_k1_relset_1, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.41       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.20/1.41  thf('118', plain,
% 1.20/1.41      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.20/1.41         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 1.20/1.41          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.20/1.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.20/1.41  thf('119', plain,
% 1.20/1.41      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.20/1.41         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['117', '118'])).
% 1.20/1.41  thf('120', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v2_funct_1 @ X0)
% 1.20/1.41          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.41          | ~ (v1_funct_1 @ X0)
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.41  thf('121', plain,
% 1.20/1.41      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.20/1.41      inference('simplify', [status(thm)], ['111'])).
% 1.20/1.41  thf('122', plain,
% 1.20/1.41      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.20/1.41         ((v4_relat_1 @ X4 @ X5)
% 1.20/1.41          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.20/1.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.41  thf('123', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('sup-', [status(thm)], ['121', '122'])).
% 1.20/1.41  thf('124', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v2_funct_1 @ X0)
% 1.20/1.41          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.41          | ~ (v1_funct_1 @ X0)
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.41  thf('125', plain,
% 1.20/1.41      (![X16 : $i, X17 : $i]:
% 1.20/1.41         (((k1_relat_1 @ X17) != (X16))
% 1.20/1.41          | (v1_partfun1 @ X17 @ X16)
% 1.20/1.41          | ~ (v4_relat_1 @ X17 @ X16)
% 1.20/1.41          | ~ (v1_relat_1 @ X17))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.20/1.41  thf('126', plain,
% 1.20/1.41      (![X17 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X17)
% 1.20/1.41          | ~ (v4_relat_1 @ X17 @ (k1_relat_1 @ X17))
% 1.20/1.41          | (v1_partfun1 @ X17 @ (k1_relat_1 @ X17)))),
% 1.20/1.41      inference('simplify', [status(thm)], ['125'])).
% 1.20/1.41  thf('127', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.41          | ~ (v1_relat_1 @ X0)
% 1.20/1.41          | ~ (v1_funct_1 @ X0)
% 1.20/1.41          | ~ (v2_funct_1 @ X0)
% 1.20/1.41          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.41          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['124', '126'])).
% 1.20/1.41  thf('128', plain,
% 1.20/1.41      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.41        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.41           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.20/1.41        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.41        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.41        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.41      inference('sup-', [status(thm)], ['123', '127'])).
% 1.20/1.41  thf('129', plain,
% 1.20/1.41      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.41        (k1_zfmisc_1 @ 
% 1.20/1.41         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.20/1.41      inference('simplify', [status(thm)], ['111'])).
% 1.20/1.41  thf('130', plain,
% 1.20/1.41      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.41         ((v1_relat_1 @ X1)
% 1.20/1.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 1.20/1.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.41  thf('131', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.20/1.41      inference('sup-', [status(thm)], ['129', '130'])).
% 1.20/1.41  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.41      inference('sup-', [status(thm)], ['42', '43'])).
% 1.20/1.41  thf('135', plain,
% 1.20/1.41      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.41      inference('demod', [status(thm)], ['128', '131', '132', '133', '134'])).
% 1.20/1.41  thf('136', plain,
% 1.20/1.41      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.20/1.41        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.41        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.41        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.41      inference('sup+', [status(thm)], ['120', '135'])).
% 1.20/1.41  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.41      inference('sup-', [status(thm)], ['42', '43'])).
% 1.20/1.41  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('140', plain,
% 1.20/1.41      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 1.20/1.41  thf('141', plain,
% 1.20/1.41      (![X16 : $i, X17 : $i]:
% 1.20/1.41         (~ (v1_partfun1 @ X17 @ X16)
% 1.20/1.41          | ((k1_relat_1 @ X17) = (X16))
% 1.20/1.41          | ~ (v4_relat_1 @ X17 @ X16)
% 1.20/1.41          | ~ (v1_relat_1 @ X17))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.20/1.41  thf('142', plain,
% 1.20/1.41      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.41        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.20/1.41        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['140', '141'])).
% 1.20/1.41  thf('143', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.20/1.41      inference('sup-', [status(thm)], ['129', '130'])).
% 1.20/1.41  thf('144', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('sup-', [status(thm)], ['121', '122'])).
% 1.20/1.41  thf('145', plain,
% 1.20/1.41      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['142', '143', '144'])).
% 1.20/1.41  thf('146', plain,
% 1.20/1.41      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.20/1.41         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['119', '145'])).
% 1.20/1.41  thf('147', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('148', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('149', plain,
% 1.20/1.41      (![X21 : $i]:
% 1.20/1.41         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.20/1.41  thf('150', plain,
% 1.20/1.41      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          != (k2_struct_0 @ sk_B)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('split', [status(esa)], ['3'])).
% 1.20/1.41  thf('151', plain,
% 1.20/1.41      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41           != (k2_struct_0 @ sk_B))
% 1.20/1.41         | ~ (l1_struct_0 @ sk_B)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['149', '150'])).
% 1.20/1.41  thf('152', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('153', plain,
% 1.20/1.41      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          != (k2_struct_0 @ sk_B)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('demod', [status(thm)], ['151', '152'])).
% 1.20/1.41  thf('154', plain,
% 1.20/1.41      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41           != (k2_struct_0 @ sk_B))
% 1.20/1.41         | ~ (l1_struct_0 @ sk_B)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['148', '153'])).
% 1.20/1.41  thf('155', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('156', plain,
% 1.20/1.41      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          != (k2_struct_0 @ sk_B)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('demod', [status(thm)], ['154', '155'])).
% 1.20/1.41  thf('157', plain,
% 1.20/1.41      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.20/1.41          != (k2_struct_0 @ sk_B)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['147', '156'])).
% 1.20/1.41  thf('158', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('159', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('160', plain,
% 1.20/1.41      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.20/1.41          != (k2_relat_1 @ sk_C)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('demod', [status(thm)], ['157', '158', '159'])).
% 1.20/1.41  thf('161', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('demod', [status(thm)], ['41', '44', '47'])).
% 1.20/1.41  thf('162', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('demod', [status(thm)], ['41', '44', '47'])).
% 1.20/1.41  thf('163', plain,
% 1.20/1.41      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.20/1.41         = (k2_funct_1 @ sk_C))),
% 1.20/1.41      inference('simplify', [status(thm)], ['102'])).
% 1.20/1.41  thf('164', plain,
% 1.20/1.41      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.20/1.41          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 1.20/1.41  thf('165', plain,
% 1.20/1.41      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.20/1.41         <= (~
% 1.20/1.41             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41                = (k2_struct_0 @ sk_B))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['146', '164'])).
% 1.20/1.41  thf('166', plain,
% 1.20/1.41      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          = (k2_struct_0 @ sk_B)))),
% 1.20/1.41      inference('simplify', [status(thm)], ['165'])).
% 1.20/1.41  thf('167', plain,
% 1.20/1.41      (~
% 1.20/1.41       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          = (k2_struct_0 @ sk_A))) | 
% 1.20/1.41       ~
% 1.20/1.41       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          = (k2_struct_0 @ sk_B)))),
% 1.20/1.41      inference('split', [status(esa)], ['3'])).
% 1.20/1.41  thf('168', plain,
% 1.20/1.41      (~
% 1.20/1.41       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.20/1.41          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.20/1.41          = (k2_struct_0 @ sk_A)))),
% 1.20/1.41      inference('sat_resolution*', [status(thm)], ['166', '167'])).
% 1.20/1.41  thf('169', plain,
% 1.20/1.41      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.20/1.41      inference('simpl_trail', [status(thm)], ['116', '168'])).
% 1.20/1.41  thf('170', plain,
% 1.20/1.41      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.20/1.41        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.41        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.41        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.41      inference('sup-', [status(thm)], ['0', '169'])).
% 1.20/1.41  thf('171', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.41      inference('sup-', [status(thm)], ['42', '43'])).
% 1.20/1.41  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('174', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 1.20/1.41      inference('demod', [status(thm)], ['170', '171', '172', '173'])).
% 1.20/1.41  thf('175', plain, ($false), inference('simplify', [status(thm)], ['174'])).
% 1.20/1.41  
% 1.20/1.41  % SZS output end Refutation
% 1.20/1.41  
% 1.20/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
