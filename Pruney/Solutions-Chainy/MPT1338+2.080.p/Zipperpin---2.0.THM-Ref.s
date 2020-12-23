%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b5qaG0l7HN

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:01 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  228 (4154 expanded)
%              Number of leaves         :   37 (1201 expanded)
%              Depth                    :   31
%              Number of atoms          : 2040 (103437 expanded)
%              Number of equality atoms :  128 (5257 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
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

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('35',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','43'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','51','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','51','54'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('58',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','43'])).

thf('71',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('78',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('79',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['68','80'])).

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

thf('82',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','79'])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('110',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','79'])).

thf('112',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84','97','98','112'])).

thf('114',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['68','80'])).

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

thf('116',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('120',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','79'])).

thf('127',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','55','56','57','114','125','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('129',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('130',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('133',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('134',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('136',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != X17 )
      | ( v1_partfun1 @ X18 @ X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('137',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v4_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
      | ( v1_partfun1 @ X18 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','138'])).

thf('140',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('144',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('148',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','144','145','146','147'])).

thf('149',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['131','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('157',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('158',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','158'])).

thf('160',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('161',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('163',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('164',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('165',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('170',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','51','54'])).

thf('172',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','51','54'])).

thf('173',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['161','173'])).

thf('175',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','174'])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('177',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','178'])).

thf('180',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('182',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['180','181'])).

thf('183',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['127','182'])).

thf('184',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,(
    $false ),
    inference(simplify,[status(thm)],['188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b5qaG0l7HN
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:30:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.66/1.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.66/1.86  % Solved by: fo/fo7.sh
% 1.66/1.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.86  % done 304 iterations in 1.402s
% 1.66/1.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.66/1.86  % SZS output start Refutation
% 1.66/1.86  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.86  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.66/1.86  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.66/1.86  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.66/1.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.66/1.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.66/1.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.66/1.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.66/1.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.66/1.86  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.66/1.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.66/1.86  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.66/1.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.66/1.86  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.66/1.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.66/1.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.66/1.86  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.66/1.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.66/1.86  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.66/1.86  thf(sk_C_type, type, sk_C: $i).
% 1.66/1.86  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.66/1.86  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.66/1.86  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.66/1.86  thf(t55_funct_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.66/1.86       ( ( v2_funct_1 @ A ) =>
% 1.66/1.86         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.66/1.86           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.66/1.86  thf('0', plain,
% 1.66/1.86      (![X4 : $i]:
% 1.66/1.86         (~ (v2_funct_1 @ X4)
% 1.66/1.86          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 1.66/1.86          | ~ (v1_funct_1 @ X4)
% 1.66/1.86          | ~ (v1_relat_1 @ X4))),
% 1.66/1.86      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.66/1.86  thf(d3_struct_0, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.66/1.86  thf('1', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('2', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf(t62_tops_2, conjecture,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( l1_struct_0 @ A ) =>
% 1.66/1.86       ( ![B:$i]:
% 1.66/1.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.66/1.86           ( ![C:$i]:
% 1.66/1.86             ( ( ( v1_funct_1 @ C ) & 
% 1.66/1.86                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.66/1.86                 ( m1_subset_1 @
% 1.66/1.86                   C @ 
% 1.66/1.86                   ( k1_zfmisc_1 @
% 1.66/1.86                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.66/1.86               ( ( ( ( k2_relset_1 @
% 1.66/1.86                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.66/1.86                     ( k2_struct_0 @ B ) ) & 
% 1.66/1.86                   ( v2_funct_1 @ C ) ) =>
% 1.66/1.86                 ( ( ( k1_relset_1 @
% 1.66/1.86                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.66/1.86                       ( k2_tops_2 @
% 1.66/1.86                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.66/1.86                     ( k2_struct_0 @ B ) ) & 
% 1.66/1.86                   ( ( k2_relset_1 @
% 1.66/1.86                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.66/1.86                       ( k2_tops_2 @
% 1.66/1.86                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.66/1.86                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.66/1.86  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.86    (~( ![A:$i]:
% 1.66/1.86        ( ( l1_struct_0 @ A ) =>
% 1.66/1.86          ( ![B:$i]:
% 1.66/1.86            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.66/1.86              ( ![C:$i]:
% 1.66/1.86                ( ( ( v1_funct_1 @ C ) & 
% 1.66/1.86                    ( v1_funct_2 @
% 1.66/1.86                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.66/1.86                    ( m1_subset_1 @
% 1.66/1.86                      C @ 
% 1.66/1.86                      ( k1_zfmisc_1 @
% 1.66/1.86                        ( k2_zfmisc_1 @
% 1.66/1.86                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.66/1.86                  ( ( ( ( k2_relset_1 @
% 1.66/1.86                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.66/1.86                        ( k2_struct_0 @ B ) ) & 
% 1.66/1.86                      ( v2_funct_1 @ C ) ) =>
% 1.66/1.86                    ( ( ( k1_relset_1 @
% 1.66/1.86                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.66/1.86                          ( k2_tops_2 @
% 1.66/1.86                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.66/1.86                        ( k2_struct_0 @ B ) ) & 
% 1.66/1.86                      ( ( k2_relset_1 @
% 1.66/1.86                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.66/1.86                          ( k2_tops_2 @
% 1.66/1.86                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.66/1.86                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.66/1.86    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.66/1.86  thf('3', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          != (k2_struct_0 @ sk_B))
% 1.66/1.86        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86            != (k2_struct_0 @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('4', plain,
% 1.66/1.86      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          != (k2_struct_0 @ sk_A)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_A))))),
% 1.66/1.86      inference('split', [status(esa)], ['3'])).
% 1.66/1.86  thf('5', plain,
% 1.66/1.86      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86           != (k2_struct_0 @ sk_A))
% 1.66/1.86         | ~ (l1_struct_0 @ sk_B)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['2', '4'])).
% 1.66/1.86  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('7', plain,
% 1.66/1.86      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          != (k2_struct_0 @ sk_A)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_A))))),
% 1.66/1.86      inference('demod', [status(thm)], ['5', '6'])).
% 1.66/1.86  thf('8', plain,
% 1.66/1.86      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86           != (k2_struct_0 @ sk_A))
% 1.66/1.86         | ~ (l1_struct_0 @ sk_B)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['1', '7'])).
% 1.66/1.86  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('10', plain,
% 1.66/1.86      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          != (k2_struct_0 @ sk_A)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_A))))),
% 1.66/1.86      inference('demod', [status(thm)], ['8', '9'])).
% 1.66/1.86  thf('11', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(redefinition_k2_relset_1, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.66/1.86  thf('12', plain,
% 1.66/1.86      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.66/1.86         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.66/1.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.66/1.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.66/1.86  thf('13', plain,
% 1.66/1.86      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['11', '12'])).
% 1.66/1.86  thf('14', plain,
% 1.66/1.86      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('16', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('17', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('18', plain,
% 1.66/1.86      (((m1_subset_1 @ sk_C @ 
% 1.66/1.86         (k1_zfmisc_1 @ 
% 1.66/1.86          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['16', '17'])).
% 1.66/1.86  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('20', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['18', '19'])).
% 1.66/1.86  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('22', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.66/1.86      inference('demod', [status(thm)], ['20', '21'])).
% 1.66/1.86  thf(cc5_funct_2, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.66/1.86       ( ![C:$i]:
% 1.66/1.86         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.66/1.86             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.66/1.86  thf('23', plain,
% 1.66/1.86      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.66/1.86          | (v1_partfun1 @ X14 @ X15)
% 1.66/1.86          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 1.66/1.86          | ~ (v1_funct_1 @ X14)
% 1.66/1.86          | (v1_xboole_0 @ X16))),
% 1.66/1.86      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.66/1.86  thf('24', plain,
% 1.66/1.86      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | ~ (v1_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['22', '23'])).
% 1.66/1.86  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('26', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('27', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('28', plain,
% 1.66/1.86      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['26', '27'])).
% 1.66/1.86  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('30', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['28', '29'])).
% 1.66/1.86  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('32', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['30', '31'])).
% 1.66/1.86  thf('33', plain,
% 1.66/1.86      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('demod', [status(thm)], ['24', '25', '32'])).
% 1.66/1.86  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('35', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf(fc2_struct_0, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.66/1.86       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.66/1.86  thf('36', plain,
% 1.66/1.86      (![X23 : $i]:
% 1.66/1.86         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 1.66/1.86          | ~ (l1_struct_0 @ X23)
% 1.66/1.86          | (v2_struct_0 @ X23))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.66/1.86  thf('37', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.66/1.86          | ~ (l1_struct_0 @ X0)
% 1.66/1.86          | (v2_struct_0 @ X0)
% 1.66/1.86          | ~ (l1_struct_0 @ X0))),
% 1.66/1.86      inference('sup-', [status(thm)], ['35', '36'])).
% 1.66/1.86  thf('38', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         ((v2_struct_0 @ X0)
% 1.66/1.86          | ~ (l1_struct_0 @ X0)
% 1.66/1.86          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.66/1.86      inference('simplify', [status(thm)], ['37'])).
% 1.66/1.86  thf('39', plain,
% 1.66/1.86      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B)
% 1.66/1.86        | (v2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup-', [status(thm)], ['34', '38'])).
% 1.66/1.86  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('41', plain,
% 1.66/1.86      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['39', '40'])).
% 1.66/1.86  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('43', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('clc', [status(thm)], ['41', '42'])).
% 1.66/1.86  thf('44', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('clc', [status(thm)], ['33', '43'])).
% 1.66/1.86  thf(d4_partfun1, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.66/1.86       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.66/1.86  thf('45', plain,
% 1.66/1.86      (![X17 : $i, X18 : $i]:
% 1.66/1.86         (~ (v1_partfun1 @ X18 @ X17)
% 1.66/1.86          | ((k1_relat_1 @ X18) = (X17))
% 1.66/1.86          | ~ (v4_relat_1 @ X18 @ X17)
% 1.66/1.86          | ~ (v1_relat_1 @ X18))),
% 1.66/1.86      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.66/1.86  thf('46', plain,
% 1.66/1.86      ((~ (v1_relat_1 @ sk_C)
% 1.66/1.86        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['44', '45'])).
% 1.66/1.86  thf('47', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(cc2_relat_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( v1_relat_1 @ A ) =>
% 1.66/1.86       ( ![B:$i]:
% 1.66/1.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.66/1.86  thf('48', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.66/1.86          | (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1))),
% 1.66/1.86      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.66/1.86  thf('49', plain,
% 1.66/1.86      ((~ (v1_relat_1 @ 
% 1.66/1.86           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.66/1.86        | (v1_relat_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['47', '48'])).
% 1.66/1.86  thf(fc6_relat_1, axiom,
% 1.66/1.86    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.66/1.86  thf('50', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.66/1.86  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.86      inference('demod', [status(thm)], ['49', '50'])).
% 1.66/1.86  thf('52', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(cc2_relset_1, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.66/1.86  thf('53', plain,
% 1.66/1.86      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.66/1.86         ((v4_relat_1 @ X5 @ X6)
% 1.66/1.86          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.66/1.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.86  thf('54', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup-', [status(thm)], ['52', '53'])).
% 1.66/1.86  thf('55', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['46', '51', '54'])).
% 1.66/1.86  thf('56', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['46', '51', '54'])).
% 1.66/1.86  thf('57', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('58', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('59', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('60', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('61', plain,
% 1.66/1.86      (((m1_subset_1 @ sk_C @ 
% 1.66/1.86         (k1_zfmisc_1 @ 
% 1.66/1.86          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup+', [status(thm)], ['59', '60'])).
% 1.66/1.86  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('63', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['61', '62'])).
% 1.66/1.86  thf('64', plain,
% 1.66/1.86      (((m1_subset_1 @ sk_C @ 
% 1.66/1.86         (k1_zfmisc_1 @ 
% 1.66/1.86          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['58', '63'])).
% 1.66/1.86  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('66', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['64', '65'])).
% 1.66/1.86  thf('67', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('68', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.66/1.86      inference('demod', [status(thm)], ['66', '67'])).
% 1.66/1.86  thf('69', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('70', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('clc', [status(thm)], ['33', '43'])).
% 1.66/1.86  thf('71', plain,
% 1.66/1.86      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup+', [status(thm)], ['69', '70'])).
% 1.66/1.86  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('73', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['71', '72'])).
% 1.66/1.86  thf('74', plain,
% 1.66/1.86      (![X17 : $i, X18 : $i]:
% 1.66/1.86         (~ (v1_partfun1 @ X18 @ X17)
% 1.66/1.86          | ((k1_relat_1 @ X18) = (X17))
% 1.66/1.86          | ~ (v4_relat_1 @ X18 @ X17)
% 1.66/1.86          | ~ (v1_relat_1 @ X18))),
% 1.66/1.86      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.66/1.86  thf('75', plain,
% 1.66/1.86      ((~ (v1_relat_1 @ sk_C)
% 1.66/1.86        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.66/1.86        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['73', '74'])).
% 1.66/1.86  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.86      inference('demod', [status(thm)], ['49', '50'])).
% 1.66/1.86  thf('77', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['61', '62'])).
% 1.66/1.86  thf('78', plain,
% 1.66/1.86      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.66/1.86         ((v4_relat_1 @ X5 @ X6)
% 1.66/1.86          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.66/1.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.86  thf('79', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup-', [status(thm)], ['77', '78'])).
% 1.66/1.86  thf('80', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['75', '76', '79'])).
% 1.66/1.86  thf('81', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.66/1.86      inference('demod', [status(thm)], ['68', '80'])).
% 1.66/1.86  thf(d4_tops_2, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.66/1.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.86       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.66/1.86         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.66/1.86  thf('82', plain,
% 1.66/1.86      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.66/1.86         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 1.66/1.86          | ~ (v2_funct_1 @ X26)
% 1.66/1.86          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 1.66/1.86          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 1.66/1.86          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 1.66/1.86          | ~ (v1_funct_1 @ X26))),
% 1.66/1.86      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.66/1.86  thf('83', plain,
% 1.66/1.86      ((~ (v1_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.86            = (k2_funct_1 @ sk_C))
% 1.66/1.86        | ~ (v2_funct_1 @ sk_C)
% 1.66/1.86        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.86            != (k2_relat_1 @ sk_C)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['81', '82'])).
% 1.66/1.86  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('85', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('86', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('87', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('88', plain,
% 1.66/1.86      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup+', [status(thm)], ['86', '87'])).
% 1.66/1.86  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('90', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['88', '89'])).
% 1.66/1.86  thf('91', plain,
% 1.66/1.86      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['85', '90'])).
% 1.66/1.86  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('93', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['91', '92'])).
% 1.66/1.86  thf('94', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('95', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['93', '94'])).
% 1.66/1.86  thf('96', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['75', '76', '79'])).
% 1.66/1.86  thf('97', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['95', '96'])).
% 1.66/1.86  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('99', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('100', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('101', plain,
% 1.66/1.86      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('102', plain,
% 1.66/1.86      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86          = (k2_struct_0 @ sk_B))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_A))),
% 1.66/1.86      inference('sup+', [status(thm)], ['100', '101'])).
% 1.66/1.86  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('104', plain,
% 1.66/1.86      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['102', '103'])).
% 1.66/1.86  thf('105', plain,
% 1.66/1.86      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86          = (k2_struct_0 @ sk_B))
% 1.66/1.86        | ~ (l1_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['99', '104'])).
% 1.66/1.86  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('107', plain,
% 1.66/1.86      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.66/1.86         = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['105', '106'])).
% 1.66/1.86  thf('108', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('110', plain,
% 1.66/1.86      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.86         = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['107', '108', '109'])).
% 1.66/1.86  thf('111', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['75', '76', '79'])).
% 1.66/1.86  thf('112', plain,
% 1.66/1.86      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.86         = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['110', '111'])).
% 1.66/1.86  thf('113', plain,
% 1.66/1.86      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.86          = (k2_funct_1 @ sk_C))
% 1.66/1.86        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.66/1.86      inference('demod', [status(thm)], ['83', '84', '97', '98', '112'])).
% 1.66/1.86  thf('114', plain,
% 1.66/1.86      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.86         = (k2_funct_1 @ sk_C))),
% 1.66/1.86      inference('simplify', [status(thm)], ['113'])).
% 1.66/1.86  thf('115', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_C @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.66/1.86      inference('demod', [status(thm)], ['68', '80'])).
% 1.66/1.86  thf(t31_funct_2, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.66/1.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.86       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.66/1.86         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.66/1.86           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.66/1.86           ( m1_subset_1 @
% 1.66/1.86             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.66/1.86  thf('116', plain,
% 1.66/1.86      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.66/1.86         (~ (v2_funct_1 @ X19)
% 1.66/1.86          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 1.66/1.86          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 1.66/1.86             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.66/1.86          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 1.66/1.86          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 1.66/1.86          | ~ (v1_funct_1 @ X19))),
% 1.66/1.86      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.66/1.86  thf('117', plain,
% 1.66/1.86      ((~ (v1_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86           (k1_zfmisc_1 @ 
% 1.66/1.86            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.66/1.86        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.86            != (k2_relat_1 @ sk_C))
% 1.66/1.86        | ~ (v2_funct_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['115', '116'])).
% 1.66/1.86  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('119', plain,
% 1.66/1.86      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['95', '96'])).
% 1.66/1.86  thf('120', plain,
% 1.66/1.86      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.86         = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['110', '111'])).
% 1.66/1.86  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('122', plain,
% 1.66/1.86      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86         (k1_zfmisc_1 @ 
% 1.66/1.86          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.66/1.86        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.66/1.86      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 1.66/1.86  thf('123', plain,
% 1.66/1.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['122'])).
% 1.66/1.86  thf('124', plain,
% 1.66/1.86      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.66/1.86         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.66/1.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.66/1.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.66/1.86  thf('125', plain,
% 1.66/1.86      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['123', '124'])).
% 1.66/1.86  thf('126', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['75', '76', '79'])).
% 1.66/1.86  thf('127', plain,
% 1.66/1.86      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_A))))),
% 1.66/1.86      inference('demod', [status(thm)],
% 1.66/1.86                ['10', '15', '55', '56', '57', '114', '125', '126'])).
% 1.66/1.86  thf('128', plain,
% 1.66/1.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['122'])).
% 1.66/1.86  thf(redefinition_k1_relset_1, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.86       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.66/1.86  thf('129', plain,
% 1.66/1.86      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.66/1.86         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.66/1.86          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.66/1.86      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.66/1.86  thf('130', plain,
% 1.66/1.86      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['128', '129'])).
% 1.66/1.86  thf('131', plain,
% 1.66/1.86      (![X4 : $i]:
% 1.66/1.86         (~ (v2_funct_1 @ X4)
% 1.66/1.86          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 1.66/1.86          | ~ (v1_funct_1 @ X4)
% 1.66/1.86          | ~ (v1_relat_1 @ X4))),
% 1.66/1.86      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.66/1.86  thf('132', plain,
% 1.66/1.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['122'])).
% 1.66/1.86  thf('133', plain,
% 1.66/1.86      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.66/1.86         ((v4_relat_1 @ X5 @ X6)
% 1.66/1.86          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.66/1.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.86  thf('134', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['132', '133'])).
% 1.66/1.86  thf('135', plain,
% 1.66/1.86      (![X4 : $i]:
% 1.66/1.86         (~ (v2_funct_1 @ X4)
% 1.66/1.86          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 1.66/1.86          | ~ (v1_funct_1 @ X4)
% 1.66/1.86          | ~ (v1_relat_1 @ X4))),
% 1.66/1.86      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.66/1.86  thf('136', plain,
% 1.66/1.86      (![X17 : $i, X18 : $i]:
% 1.66/1.86         (((k1_relat_1 @ X18) != (X17))
% 1.66/1.86          | (v1_partfun1 @ X18 @ X17)
% 1.66/1.86          | ~ (v4_relat_1 @ X18 @ X17)
% 1.66/1.86          | ~ (v1_relat_1 @ X18))),
% 1.66/1.86      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.66/1.86  thf('137', plain,
% 1.66/1.86      (![X18 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X18)
% 1.66/1.86          | ~ (v4_relat_1 @ X18 @ (k1_relat_1 @ X18))
% 1.66/1.86          | (v1_partfun1 @ X18 @ (k1_relat_1 @ X18)))),
% 1.66/1.86      inference('simplify', [status(thm)], ['136'])).
% 1.66/1.86  thf('138', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v2_funct_1 @ X0)
% 1.66/1.86          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.66/1.86          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['135', '137'])).
% 1.66/1.86  thf('139', plain,
% 1.66/1.86      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.66/1.86        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.66/1.86        | ~ (v2_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v1_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v1_relat_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['134', '138'])).
% 1.66/1.86  thf('140', plain,
% 1.66/1.86      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.66/1.86        (k1_zfmisc_1 @ 
% 1.66/1.86         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['122'])).
% 1.66/1.86  thf('141', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.66/1.86          | (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1))),
% 1.66/1.86      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.66/1.86  thf('142', plain,
% 1.66/1.86      ((~ (v1_relat_1 @ 
% 1.66/1.86           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 1.66/1.86        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['140', '141'])).
% 1.66/1.86  thf('143', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.66/1.86  thf('144', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['142', '143'])).
% 1.66/1.86  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.86      inference('demod', [status(thm)], ['49', '50'])).
% 1.66/1.86  thf('148', plain,
% 1.66/1.86      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.66/1.86      inference('demod', [status(thm)], ['139', '144', '145', '146', '147'])).
% 1.66/1.86  thf('149', plain,
% 1.66/1.86      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | ~ (v1_relat_1 @ sk_C)
% 1.66/1.86        | ~ (v1_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v2_funct_1 @ sk_C))),
% 1.66/1.86      inference('sup+', [status(thm)], ['131', '148'])).
% 1.66/1.86  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.86      inference('demod', [status(thm)], ['49', '50'])).
% 1.66/1.86  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('153', plain,
% 1.66/1.86      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 1.66/1.86  thf('154', plain,
% 1.66/1.86      (![X17 : $i, X18 : $i]:
% 1.66/1.86         (~ (v1_partfun1 @ X18 @ X17)
% 1.66/1.86          | ((k1_relat_1 @ X18) = (X17))
% 1.66/1.86          | ~ (v4_relat_1 @ X18 @ X17)
% 1.66/1.86          | ~ (v1_relat_1 @ X18))),
% 1.66/1.86      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.66/1.86  thf('155', plain,
% 1.66/1.86      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.66/1.86        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.66/1.86        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['153', '154'])).
% 1.66/1.86  thf('156', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['142', '143'])).
% 1.66/1.86  thf('157', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['132', '133'])).
% 1.66/1.86  thf('158', plain,
% 1.66/1.86      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['155', '156', '157'])).
% 1.66/1.86  thf('159', plain,
% 1.66/1.86      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['130', '158'])).
% 1.66/1.86  thf('160', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('161', plain,
% 1.66/1.86      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.66/1.86         = (k2_funct_1 @ sk_C))),
% 1.66/1.86      inference('simplify', [status(thm)], ['113'])).
% 1.66/1.86  thf('162', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('163', plain,
% 1.66/1.86      (![X22 : $i]:
% 1.66/1.86         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.66/1.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.66/1.86  thf('164', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          != (k2_struct_0 @ sk_B)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('split', [status(esa)], ['3'])).
% 1.66/1.86  thf('165', plain,
% 1.66/1.86      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86           != (k2_struct_0 @ sk_B))
% 1.66/1.86         | ~ (l1_struct_0 @ sk_B)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['163', '164'])).
% 1.66/1.86  thf('166', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('167', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          != (k2_struct_0 @ sk_B)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['165', '166'])).
% 1.66/1.86  thf('168', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.66/1.86          != (k2_struct_0 @ sk_B)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['162', '167'])).
% 1.66/1.86  thf('169', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('170', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.66/1.86          != (k2_relat_1 @ sk_C)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['168', '169'])).
% 1.66/1.86  thf('171', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['46', '51', '54'])).
% 1.66/1.86  thf('172', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['46', '51', '54'])).
% 1.66/1.86  thf('173', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.66/1.86          != (k2_relat_1 @ sk_C)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.66/1.86  thf('174', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['161', '173'])).
% 1.66/1.86  thf('175', plain,
% 1.66/1.86      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86           (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 1.66/1.86         | ~ (l1_struct_0 @ sk_B)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['160', '174'])).
% 1.66/1.86  thf('176', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['13', '14'])).
% 1.66/1.86  thf('177', plain, ((l1_struct_0 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('178', plain,
% 1.66/1.86      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.66/1.86          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('demod', [status(thm)], ['175', '176', '177'])).
% 1.66/1.86  thf('179', plain,
% 1.66/1.86      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86                = (k2_struct_0 @ sk_B))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['159', '178'])).
% 1.66/1.86  thf('180', plain,
% 1.66/1.86      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          = (k2_struct_0 @ sk_B)))),
% 1.66/1.86      inference('simplify', [status(thm)], ['179'])).
% 1.66/1.86  thf('181', plain,
% 1.66/1.86      (~
% 1.66/1.86       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          = (k2_struct_0 @ sk_A))) | 
% 1.66/1.86       ~
% 1.66/1.86       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          = (k2_struct_0 @ sk_B)))),
% 1.66/1.86      inference('split', [status(esa)], ['3'])).
% 1.66/1.86  thf('182', plain,
% 1.66/1.86      (~
% 1.66/1.86       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.66/1.86          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.66/1.86          = (k2_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sat_resolution*', [status(thm)], ['180', '181'])).
% 1.66/1.86  thf('183', plain,
% 1.66/1.86      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.66/1.86      inference('simpl_trail', [status(thm)], ['127', '182'])).
% 1.66/1.86  thf('184', plain,
% 1.66/1.86      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.66/1.86        | ~ (v1_relat_1 @ sk_C)
% 1.66/1.86        | ~ (v1_funct_1 @ sk_C)
% 1.66/1.86        | ~ (v2_funct_1 @ sk_C))),
% 1.66/1.86      inference('sup-', [status(thm)], ['0', '183'])).
% 1.66/1.86  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 1.66/1.86      inference('demod', [status(thm)], ['49', '50'])).
% 1.66/1.86  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('187', plain, ((v2_funct_1 @ sk_C)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('188', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 1.66/1.86      inference('demod', [status(thm)], ['184', '185', '186', '187'])).
% 1.66/1.86  thf('189', plain, ($false), inference('simplify', [status(thm)], ['188'])).
% 1.66/1.86  
% 1.66/1.86  % SZS output end Refutation
% 1.66/1.86  
% 1.66/1.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
