%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONxNrhCMiE

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:01 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  225 (4038 expanded)
%              Number of leaves         :   37 (1172 expanded)
%              Depth                    :   31
%              Number of atoms          : 2017 (102567 expanded)
%              Number of equality atoms :  127 (5199 expanded)
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

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('35',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','40'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('55',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
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

thf('61',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('68',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('75',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('76',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['65','77'])).

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

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
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
    inference('sup+',[status(thm)],['13','14'])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('109',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','94','95','109'])).

thf('111',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['65','77'])).

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

thf('113',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('122',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('124',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','52','53','54','111','122','123'])).

thf('125',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('126',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('127',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('129',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('130',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('131',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('133',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != X17 )
      | ( v1_partfun1 @ X18 @ X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('134',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v4_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
      | ( v1_partfun1 @ X18 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','134'])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','135'])).

thf('137',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('141',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('145',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','141','142','143','144'])).

thf('146',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['128','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('152',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('154',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('155',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','155'])).

thf('157',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('158',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('160',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('161',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('162',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','164'])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('167',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('169',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','48','51'])).

thf('170',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','170'])).

thf('172',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','171'])).

thf('173',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('174',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','175'])).

thf('177',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('179',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['177','178'])).

thf('180',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['124','179'])).

thf('181',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','180'])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('186',plain,(
    $false ),
    inference(simplify,[status(thm)],['185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONxNrhCMiE
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.81  % Solved by: fo/fo7.sh
% 1.65/1.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.81  % done 304 iterations in 1.354s
% 1.65/1.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.81  % SZS output start Refutation
% 1.65/1.81  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.81  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.65/1.81  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.65/1.81  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.65/1.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.65/1.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.81  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.65/1.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.81  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.65/1.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.65/1.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.81  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.65/1.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.65/1.81  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.81  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.65/1.81  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.65/1.81  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.65/1.81  thf(t55_funct_1, axiom,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.81       ( ( v2_funct_1 @ A ) =>
% 1.65/1.81         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.65/1.81           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.65/1.81  thf('0', plain,
% 1.65/1.81      (![X4 : $i]:
% 1.65/1.81         (~ (v2_funct_1 @ X4)
% 1.65/1.81          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 1.65/1.81          | ~ (v1_funct_1 @ X4)
% 1.65/1.81          | ~ (v1_relat_1 @ X4))),
% 1.65/1.81      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.81  thf(d3_struct_0, axiom,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.65/1.81  thf('1', plain,
% 1.65/1.81      (![X22 : $i]:
% 1.65/1.81         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.81  thf('2', plain,
% 1.65/1.81      (![X22 : $i]:
% 1.65/1.81         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.81  thf(t62_tops_2, conjecture,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( l1_struct_0 @ A ) =>
% 1.65/1.81       ( ![B:$i]:
% 1.65/1.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.65/1.81           ( ![C:$i]:
% 1.65/1.81             ( ( ( v1_funct_1 @ C ) & 
% 1.65/1.81                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.81                 ( m1_subset_1 @
% 1.65/1.81                   C @ 
% 1.65/1.81                   ( k1_zfmisc_1 @
% 1.65/1.81                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.81               ( ( ( ( k2_relset_1 @
% 1.65/1.81                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.65/1.81                     ( k2_struct_0 @ B ) ) & 
% 1.65/1.81                   ( v2_funct_1 @ C ) ) =>
% 1.65/1.81                 ( ( ( k1_relset_1 @
% 1.65/1.81                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.65/1.81                       ( k2_tops_2 @
% 1.65/1.81                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.65/1.81                     ( k2_struct_0 @ B ) ) & 
% 1.65/1.81                   ( ( k2_relset_1 @
% 1.65/1.81                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.65/1.81                       ( k2_tops_2 @
% 1.65/1.81                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.65/1.81                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.65/1.81  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.81    (~( ![A:$i]:
% 1.65/1.81        ( ( l1_struct_0 @ A ) =>
% 1.65/1.81          ( ![B:$i]:
% 1.65/1.81            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.65/1.81              ( ![C:$i]:
% 1.65/1.81                ( ( ( v1_funct_1 @ C ) & 
% 1.65/1.81                    ( v1_funct_2 @
% 1.65/1.81                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.65/1.81                    ( m1_subset_1 @
% 1.65/1.81                      C @ 
% 1.65/1.81                      ( k1_zfmisc_1 @
% 1.65/1.81                        ( k2_zfmisc_1 @
% 1.65/1.81                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.65/1.81                  ( ( ( ( k2_relset_1 @
% 1.65/1.81                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.65/1.81                        ( k2_struct_0 @ B ) ) & 
% 1.65/1.81                      ( v2_funct_1 @ C ) ) =>
% 1.65/1.81                    ( ( ( k1_relset_1 @
% 1.65/1.81                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.65/1.81                          ( k2_tops_2 @
% 1.65/1.81                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.65/1.81                        ( k2_struct_0 @ B ) ) & 
% 1.65/1.81                      ( ( k2_relset_1 @
% 1.65/1.81                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.65/1.81                          ( k2_tops_2 @
% 1.65/1.81                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.65/1.81                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.65/1.81    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.65/1.81  thf('3', plain,
% 1.65/1.81      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81          != (k2_struct_0 @ sk_B))
% 1.65/1.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81            != (k2_struct_0 @ sk_A)))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('4', plain,
% 1.65/1.81      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81          != (k2_struct_0 @ sk_A)))
% 1.65/1.81         <= (~
% 1.65/1.81             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81                = (k2_struct_0 @ sk_A))))),
% 1.65/1.81      inference('split', [status(esa)], ['3'])).
% 1.65/1.81  thf('5', plain,
% 1.65/1.81      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81           != (k2_struct_0 @ sk_A))
% 1.65/1.81         | ~ (l1_struct_0 @ sk_B)))
% 1.65/1.81         <= (~
% 1.65/1.81             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81                = (k2_struct_0 @ sk_A))))),
% 1.65/1.81      inference('sup-', [status(thm)], ['2', '4'])).
% 1.65/1.81  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('7', plain,
% 1.65/1.81      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81          != (k2_struct_0 @ sk_A)))
% 1.65/1.81         <= (~
% 1.65/1.81             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81                = (k2_struct_0 @ sk_A))))),
% 1.65/1.81      inference('demod', [status(thm)], ['5', '6'])).
% 1.65/1.81  thf('8', plain,
% 1.65/1.81      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81           != (k2_struct_0 @ sk_A))
% 1.65/1.81         | ~ (l1_struct_0 @ sk_B)))
% 1.65/1.81         <= (~
% 1.65/1.81             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81                = (k2_struct_0 @ sk_A))))),
% 1.65/1.81      inference('sup-', [status(thm)], ['1', '7'])).
% 1.65/1.81  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('10', plain,
% 1.65/1.81      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81          != (k2_struct_0 @ sk_A)))
% 1.65/1.81         <= (~
% 1.65/1.81             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.81                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.81                = (k2_struct_0 @ sk_A))))),
% 1.65/1.81      inference('demod', [status(thm)], ['8', '9'])).
% 1.65/1.81  thf('11', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C @ 
% 1.65/1.81        (k1_zfmisc_1 @ 
% 1.65/1.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(redefinition_k2_relset_1, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.81       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.65/1.81  thf('12', plain,
% 1.65/1.81      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.65/1.81         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.65/1.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.65/1.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.81  thf('13', plain,
% 1.65/1.81      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.65/1.81         = (k2_relat_1 @ sk_C))),
% 1.65/1.81      inference('sup-', [status(thm)], ['11', '12'])).
% 1.65/1.81  thf('14', plain,
% 1.65/1.81      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.65/1.81         = (k2_struct_0 @ sk_B))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.81      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.81  thf('16', plain,
% 1.65/1.81      (![X22 : $i]:
% 1.65/1.81         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.81  thf('17', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C @ 
% 1.65/1.81        (k1_zfmisc_1 @ 
% 1.65/1.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('18', plain,
% 1.65/1.81      (((m1_subset_1 @ sk_C @ 
% 1.65/1.81         (k1_zfmisc_1 @ 
% 1.65/1.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.65/1.81        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.81      inference('sup+', [status(thm)], ['16', '17'])).
% 1.65/1.81  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('20', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C @ 
% 1.65/1.81        (k1_zfmisc_1 @ 
% 1.65/1.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.65/1.81      inference('demod', [status(thm)], ['18', '19'])).
% 1.65/1.81  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.81      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.81  thf('22', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C @ 
% 1.65/1.81        (k1_zfmisc_1 @ 
% 1.65/1.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.65/1.81      inference('demod', [status(thm)], ['20', '21'])).
% 1.65/1.81  thf(cc5_funct_2, axiom,
% 1.65/1.81    (![A:$i,B:$i]:
% 1.65/1.81     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.65/1.81       ( ![C:$i]:
% 1.65/1.81         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.81           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.65/1.81             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.65/1.81  thf('23', plain,
% 1.65/1.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.81         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.65/1.81          | (v1_partfun1 @ X14 @ X15)
% 1.65/1.81          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 1.65/1.81          | ~ (v1_funct_1 @ X14)
% 1.65/1.81          | (v1_xboole_0 @ X16))),
% 1.65/1.81      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.65/1.81  thf('24', plain,
% 1.65/1.81      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.65/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.81        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.65/1.81        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['22', '23'])).
% 1.65/1.81  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('26', plain,
% 1.65/1.81      (![X22 : $i]:
% 1.65/1.81         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.81  thf('27', plain,
% 1.65/1.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('28', plain,
% 1.65/1.81      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.65/1.81        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.81      inference('sup+', [status(thm)], ['26', '27'])).
% 1.65/1.81  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('30', plain,
% 1.65/1.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.65/1.81      inference('demod', [status(thm)], ['28', '29'])).
% 1.65/1.81  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.81      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.81  thf('32', plain,
% 1.65/1.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.65/1.81      inference('demod', [status(thm)], ['30', '31'])).
% 1.65/1.81  thf('33', plain,
% 1.65/1.81      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.65/1.81        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.65/1.81      inference('demod', [status(thm)], ['24', '25', '32'])).
% 1.65/1.81  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.81      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.81  thf(fc5_struct_0, axiom,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.65/1.81       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.65/1.81  thf('35', plain,
% 1.65/1.81      (![X23 : $i]:
% 1.65/1.81         (~ (v1_xboole_0 @ (k2_struct_0 @ X23))
% 1.65/1.81          | ~ (l1_struct_0 @ X23)
% 1.65/1.81          | (v2_struct_0 @ X23))),
% 1.65/1.81      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.65/1.81  thf('36', plain,
% 1.65/1.81      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.65/1.81        | (v2_struct_0 @ sk_B)
% 1.65/1.81        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.81      inference('sup-', [status(thm)], ['34', '35'])).
% 1.65/1.81  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('38', plain,
% 1.65/1.81      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.65/1.81      inference('demod', [status(thm)], ['36', '37'])).
% 1.65/1.81  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('40', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.65/1.81      inference('clc', [status(thm)], ['38', '39'])).
% 1.65/1.81  thf('41', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.65/1.81      inference('clc', [status(thm)], ['33', '40'])).
% 1.65/1.81  thf(d4_partfun1, axiom,
% 1.65/1.81    (![A:$i,B:$i]:
% 1.65/1.81     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.65/1.81       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.65/1.81  thf('42', plain,
% 1.65/1.81      (![X17 : $i, X18 : $i]:
% 1.65/1.81         (~ (v1_partfun1 @ X18 @ X17)
% 1.65/1.81          | ((k1_relat_1 @ X18) = (X17))
% 1.65/1.81          | ~ (v4_relat_1 @ X18 @ X17)
% 1.65/1.81          | ~ (v1_relat_1 @ X18))),
% 1.65/1.81      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.65/1.81  thf('43', plain,
% 1.65/1.81      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.81        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.65/1.81        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.65/1.81      inference('sup-', [status(thm)], ['41', '42'])).
% 1.65/1.81  thf('44', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C @ 
% 1.65/1.81        (k1_zfmisc_1 @ 
% 1.65/1.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(cc2_relat_1, axiom,
% 1.65/1.81    (![A:$i]:
% 1.65/1.81     ( ( v1_relat_1 @ A ) =>
% 1.65/1.81       ( ![B:$i]:
% 1.65/1.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.65/1.81  thf('45', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.65/1.81          | (v1_relat_1 @ X0)
% 1.65/1.81          | ~ (v1_relat_1 @ X1))),
% 1.65/1.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.81  thf('46', plain,
% 1.65/1.81      ((~ (v1_relat_1 @ 
% 1.65/1.81           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.65/1.81        | (v1_relat_1 @ sk_C))),
% 1.65/1.81      inference('sup-', [status(thm)], ['44', '45'])).
% 1.65/1.81  thf(fc6_relat_1, axiom,
% 1.65/1.81    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.65/1.81  thf('47', plain,
% 1.65/1.81      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.65/1.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.81  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.81      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.81  thf('49', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C @ 
% 1.65/1.81        (k1_zfmisc_1 @ 
% 1.65/1.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(cc2_relset_1, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.65/1.81  thf('50', plain,
% 1.65/1.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.65/1.81         ((v4_relat_1 @ X5 @ X6)
% 1.65/1.81          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.65/1.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.81  thf('51', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.65/1.81      inference('sup-', [status(thm)], ['49', '50'])).
% 1.65/1.81  thf('52', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.65/1.81  thf('53', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.65/1.81      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.65/1.81  thf('54', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.81      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.81  thf('55', plain,
% 1.65/1.81      (![X22 : $i]:
% 1.65/1.81         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.81  thf('56', plain,
% 1.65/1.81      (![X22 : $i]:
% 1.65/1.81         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.81  thf('57', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C @ 
% 1.65/1.81        (k1_zfmisc_1 @ 
% 1.65/1.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('58', plain,
% 1.65/1.81      (((m1_subset_1 @ sk_C @ 
% 1.65/1.81         (k1_zfmisc_1 @ 
% 1.65/1.81          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.65/1.81        | ~ (l1_struct_0 @ sk_A))),
% 1.65/1.81      inference('sup+', [status(thm)], ['56', '57'])).
% 1.65/1.81  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf('60', plain,
% 1.65/1.81      ((m1_subset_1 @ sk_C @ 
% 1.65/1.81        (k1_zfmisc_1 @ 
% 1.65/1.81         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.81      inference('demod', [status(thm)], ['58', '59'])).
% 1.65/1.81  thf('61', plain,
% 1.65/1.81      (((m1_subset_1 @ sk_C @ 
% 1.65/1.82         (k1_zfmisc_1 @ 
% 1.65/1.82          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.65/1.82        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['55', '60'])).
% 1.65/1.82  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('63', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_C @ 
% 1.65/1.82        (k1_zfmisc_1 @ 
% 1.65/1.82         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('demod', [status(thm)], ['61', '62'])).
% 1.65/1.82  thf('64', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.82  thf('65', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_C @ 
% 1.65/1.82        (k1_zfmisc_1 @ 
% 1.65/1.82         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.65/1.82      inference('demod', [status(thm)], ['63', '64'])).
% 1.65/1.82  thf('66', plain,
% 1.65/1.82      (![X22 : $i]:
% 1.65/1.82         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.82  thf('67', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.65/1.82      inference('clc', [status(thm)], ['33', '40'])).
% 1.65/1.82  thf('68', plain,
% 1.65/1.82      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.65/1.82      inference('sup+', [status(thm)], ['66', '67'])).
% 1.65/1.82  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('70', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.65/1.82      inference('demod', [status(thm)], ['68', '69'])).
% 1.65/1.82  thf('71', plain,
% 1.65/1.82      (![X17 : $i, X18 : $i]:
% 1.65/1.82         (~ (v1_partfun1 @ X18 @ X17)
% 1.65/1.82          | ((k1_relat_1 @ X18) = (X17))
% 1.65/1.82          | ~ (v4_relat_1 @ X18 @ X17)
% 1.65/1.82          | ~ (v1_relat_1 @ X18))),
% 1.65/1.82      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.65/1.82  thf('72', plain,
% 1.65/1.82      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.82        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.65/1.82        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['70', '71'])).
% 1.65/1.82  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.82      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.82  thf('74', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_C @ 
% 1.65/1.82        (k1_zfmisc_1 @ 
% 1.65/1.82         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.65/1.82      inference('demod', [status(thm)], ['58', '59'])).
% 1.65/1.82  thf('75', plain,
% 1.65/1.82      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.65/1.82         ((v4_relat_1 @ X5 @ X6)
% 1.65/1.82          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.65/1.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.82  thf('76', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.65/1.82      inference('sup-', [status(thm)], ['74', '75'])).
% 1.65/1.82  thf('77', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.65/1.82      inference('demod', [status(thm)], ['72', '73', '76'])).
% 1.65/1.82  thf('78', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_C @ 
% 1.65/1.82        (k1_zfmisc_1 @ 
% 1.65/1.82         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.65/1.82      inference('demod', [status(thm)], ['65', '77'])).
% 1.65/1.82  thf(d4_tops_2, axiom,
% 1.65/1.82    (![A:$i,B:$i,C:$i]:
% 1.65/1.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.82       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.65/1.82         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.65/1.82  thf('79', plain,
% 1.65/1.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.65/1.82         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 1.65/1.82          | ~ (v2_funct_1 @ X26)
% 1.65/1.82          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 1.65/1.82          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 1.65/1.82          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 1.65/1.82          | ~ (v1_funct_1 @ X26))),
% 1.65/1.82      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.65/1.82  thf('80', plain,
% 1.65/1.82      ((~ (v1_funct_1 @ sk_C)
% 1.65/1.82        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.65/1.82        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.82            = (k2_funct_1 @ sk_C))
% 1.65/1.82        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.82        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.82            != (k2_relat_1 @ sk_C)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['78', '79'])).
% 1.65/1.82  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('82', plain,
% 1.65/1.82      (![X22 : $i]:
% 1.65/1.82         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.82  thf('83', plain,
% 1.65/1.82      (![X22 : $i]:
% 1.65/1.82         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.82  thf('84', plain,
% 1.65/1.82      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('85', plain,
% 1.65/1.82      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.65/1.82        | ~ (l1_struct_0 @ sk_A))),
% 1.65/1.82      inference('sup+', [status(thm)], ['83', '84'])).
% 1.65/1.82  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('87', plain,
% 1.65/1.82      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.65/1.82      inference('demod', [status(thm)], ['85', '86'])).
% 1.65/1.82  thf('88', plain,
% 1.65/1.82      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.65/1.82        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['82', '87'])).
% 1.65/1.82  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('90', plain,
% 1.65/1.82      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.82  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.82  thf('92', plain,
% 1.65/1.82      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['90', '91'])).
% 1.65/1.82  thf('93', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.65/1.82      inference('demod', [status(thm)], ['72', '73', '76'])).
% 1.65/1.82  thf('94', plain,
% 1.65/1.82      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.82  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('96', plain,
% 1.65/1.82      (![X22 : $i]:
% 1.65/1.82         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.82  thf('97', plain,
% 1.65/1.82      (![X22 : $i]:
% 1.65/1.82         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.82  thf('98', plain,
% 1.65/1.82      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.65/1.82         = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('99', plain,
% 1.65/1.82      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.65/1.82          = (k2_struct_0 @ sk_B))
% 1.65/1.82        | ~ (l1_struct_0 @ sk_A))),
% 1.65/1.82      inference('sup+', [status(thm)], ['97', '98'])).
% 1.65/1.82  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('101', plain,
% 1.65/1.82      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.65/1.82         = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('demod', [status(thm)], ['99', '100'])).
% 1.65/1.82  thf('102', plain,
% 1.65/1.82      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.65/1.82          = (k2_struct_0 @ sk_B))
% 1.65/1.82        | ~ (l1_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['96', '101'])).
% 1.65/1.82  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('104', plain,
% 1.65/1.82      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.65/1.82         = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('demod', [status(thm)], ['102', '103'])).
% 1.65/1.82  thf('105', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.82  thf('106', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.82  thf('107', plain,
% 1.65/1.82      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.82         = (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.65/1.82  thf('108', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.65/1.82      inference('demod', [status(thm)], ['72', '73', '76'])).
% 1.65/1.82  thf('109', plain,
% 1.65/1.82      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.82         = (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['107', '108'])).
% 1.65/1.82  thf('110', plain,
% 1.65/1.82      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.82          = (k2_funct_1 @ sk_C))
% 1.65/1.82        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.65/1.82      inference('demod', [status(thm)], ['80', '81', '94', '95', '109'])).
% 1.65/1.82  thf('111', plain,
% 1.65/1.82      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.82         = (k2_funct_1 @ sk_C))),
% 1.65/1.82      inference('simplify', [status(thm)], ['110'])).
% 1.65/1.82  thf('112', plain,
% 1.65/1.82      ((m1_subset_1 @ sk_C @ 
% 1.65/1.82        (k1_zfmisc_1 @ 
% 1.65/1.82         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.65/1.82      inference('demod', [status(thm)], ['65', '77'])).
% 1.65/1.82  thf(t31_funct_2, axiom,
% 1.65/1.82    (![A:$i,B:$i,C:$i]:
% 1.65/1.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.82       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.65/1.82         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.65/1.82           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.65/1.82           ( m1_subset_1 @
% 1.65/1.82             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.65/1.82  thf('113', plain,
% 1.65/1.82      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.65/1.82         (~ (v2_funct_1 @ X19)
% 1.65/1.82          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 1.65/1.82          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 1.65/1.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.65/1.82          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 1.65/1.82          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 1.65/1.82          | ~ (v1_funct_1 @ X19))),
% 1.65/1.82      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.65/1.82  thf('114', plain,
% 1.65/1.82      ((~ (v1_funct_1 @ sk_C)
% 1.65/1.82        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.65/1.82        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.82           (k1_zfmisc_1 @ 
% 1.65/1.82            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.65/1.82        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.82            != (k2_relat_1 @ sk_C))
% 1.65/1.82        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.82      inference('sup-', [status(thm)], ['112', '113'])).
% 1.65/1.82  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('116', plain,
% 1.65/1.82      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.82  thf('117', plain,
% 1.65/1.82      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.82         = (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['107', '108'])).
% 1.65/1.82  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('119', plain,
% 1.65/1.82      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.82         (k1_zfmisc_1 @ 
% 1.65/1.82          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.65/1.82        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.65/1.82      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 1.65/1.82  thf('120', plain,
% 1.65/1.82      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.82        (k1_zfmisc_1 @ 
% 1.65/1.82         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.65/1.82      inference('simplify', [status(thm)], ['119'])).
% 1.65/1.82  thf('121', plain,
% 1.65/1.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.65/1.82         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.65/1.82          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.65/1.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.82  thf('122', plain,
% 1.65/1.82      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.82         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['120', '121'])).
% 1.65/1.82  thf('123', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.65/1.82      inference('demod', [status(thm)], ['72', '73', '76'])).
% 1.65/1.82  thf('124', plain,
% 1.65/1.82      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_A))))),
% 1.65/1.82      inference('demod', [status(thm)],
% 1.65/1.82                ['10', '15', '52', '53', '54', '111', '122', '123'])).
% 1.65/1.82  thf('125', plain,
% 1.65/1.82      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.82        (k1_zfmisc_1 @ 
% 1.65/1.82         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.65/1.82      inference('simplify', [status(thm)], ['119'])).
% 1.65/1.82  thf(redefinition_k1_relset_1, axiom,
% 1.65/1.82    (![A:$i,B:$i,C:$i]:
% 1.65/1.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.65/1.82  thf('126', plain,
% 1.65/1.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.65/1.82         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.65/1.82          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.65/1.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.65/1.82  thf('127', plain,
% 1.65/1.82      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.82         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['125', '126'])).
% 1.65/1.82  thf('128', plain,
% 1.65/1.82      (![X4 : $i]:
% 1.65/1.82         (~ (v2_funct_1 @ X4)
% 1.65/1.82          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 1.65/1.82          | ~ (v1_funct_1 @ X4)
% 1.65/1.82          | ~ (v1_relat_1 @ X4))),
% 1.65/1.82      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.82  thf('129', plain,
% 1.65/1.82      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.82        (k1_zfmisc_1 @ 
% 1.65/1.82         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.65/1.82      inference('simplify', [status(thm)], ['119'])).
% 1.65/1.82  thf('130', plain,
% 1.65/1.82      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.65/1.82         ((v4_relat_1 @ X5 @ X6)
% 1.65/1.82          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.65/1.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.82  thf('131', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('sup-', [status(thm)], ['129', '130'])).
% 1.65/1.82  thf('132', plain,
% 1.65/1.82      (![X4 : $i]:
% 1.65/1.82         (~ (v2_funct_1 @ X4)
% 1.65/1.82          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 1.65/1.82          | ~ (v1_funct_1 @ X4)
% 1.65/1.82          | ~ (v1_relat_1 @ X4))),
% 1.65/1.82      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.82  thf('133', plain,
% 1.65/1.82      (![X17 : $i, X18 : $i]:
% 1.65/1.82         (((k1_relat_1 @ X18) != (X17))
% 1.65/1.82          | (v1_partfun1 @ X18 @ X17)
% 1.65/1.82          | ~ (v4_relat_1 @ X18 @ X17)
% 1.65/1.82          | ~ (v1_relat_1 @ X18))),
% 1.65/1.82      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.65/1.82  thf('134', plain,
% 1.65/1.82      (![X18 : $i]:
% 1.65/1.82         (~ (v1_relat_1 @ X18)
% 1.65/1.82          | ~ (v4_relat_1 @ X18 @ (k1_relat_1 @ X18))
% 1.65/1.82          | (v1_partfun1 @ X18 @ (k1_relat_1 @ X18)))),
% 1.65/1.82      inference('simplify', [status(thm)], ['133'])).
% 1.65/1.82  thf('135', plain,
% 1.65/1.82      (![X0 : $i]:
% 1.65/1.82         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.82          | ~ (v1_relat_1 @ X0)
% 1.65/1.82          | ~ (v1_funct_1 @ X0)
% 1.65/1.82          | ~ (v2_funct_1 @ X0)
% 1.65/1.82          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['132', '134'])).
% 1.65/1.82  thf('136', plain,
% 1.65/1.82      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.82        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.82           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.65/1.82        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.82        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.82        | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.82      inference('sup-', [status(thm)], ['131', '135'])).
% 1.65/1.82  thf('137', plain,
% 1.65/1.82      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.82        (k1_zfmisc_1 @ 
% 1.65/1.82         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.65/1.82      inference('simplify', [status(thm)], ['119'])).
% 1.65/1.82  thf('138', plain,
% 1.65/1.82      (![X0 : $i, X1 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.65/1.82          | (v1_relat_1 @ X0)
% 1.65/1.82          | ~ (v1_relat_1 @ X1))),
% 1.65/1.82      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.82  thf('139', plain,
% 1.65/1.82      ((~ (v1_relat_1 @ 
% 1.65/1.82           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 1.65/1.82        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['137', '138'])).
% 1.65/1.82  thf('140', plain,
% 1.65/1.82      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.65/1.82      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.82  thf('141', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['139', '140'])).
% 1.65/1.82  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.82      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.82  thf('145', plain,
% 1.65/1.82      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.82      inference('demod', [status(thm)], ['136', '141', '142', '143', '144'])).
% 1.65/1.82  thf('146', plain,
% 1.65/1.82      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.65/1.82        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.82        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.82        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.82      inference('sup+', [status(thm)], ['128', '145'])).
% 1.65/1.82  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.82      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.82  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('150', plain,
% 1.65/1.82      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 1.65/1.82  thf('151', plain,
% 1.65/1.82      (![X17 : $i, X18 : $i]:
% 1.65/1.82         (~ (v1_partfun1 @ X18 @ X17)
% 1.65/1.82          | ((k1_relat_1 @ X18) = (X17))
% 1.65/1.82          | ~ (v4_relat_1 @ X18 @ X17)
% 1.65/1.82          | ~ (v1_relat_1 @ X18))),
% 1.65/1.82      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.65/1.82  thf('152', plain,
% 1.65/1.82      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.82        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.65/1.82        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['150', '151'])).
% 1.65/1.82  thf('153', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['139', '140'])).
% 1.65/1.82  thf('154', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('sup-', [status(thm)], ['129', '130'])).
% 1.65/1.82  thf('155', plain,
% 1.65/1.82      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.65/1.82  thf('156', plain,
% 1.65/1.82      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.82         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['127', '155'])).
% 1.65/1.82  thf('157', plain,
% 1.65/1.82      (![X22 : $i]:
% 1.65/1.82         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.82  thf('158', plain,
% 1.65/1.82      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.65/1.82         = (k2_funct_1 @ sk_C))),
% 1.65/1.82      inference('simplify', [status(thm)], ['110'])).
% 1.65/1.82  thf('159', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.82  thf('160', plain,
% 1.65/1.82      (![X22 : $i]:
% 1.65/1.82         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 1.65/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.65/1.82  thf('161', plain,
% 1.65/1.82      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82          != (k2_struct_0 @ sk_B)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('split', [status(esa)], ['3'])).
% 1.65/1.82  thf('162', plain,
% 1.65/1.82      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82           != (k2_struct_0 @ sk_B))
% 1.65/1.82         | ~ (l1_struct_0 @ sk_B)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['160', '161'])).
% 1.65/1.82  thf('163', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('164', plain,
% 1.65/1.82      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82          != (k2_struct_0 @ sk_B)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('demod', [status(thm)], ['162', '163'])).
% 1.65/1.82  thf('165', plain,
% 1.65/1.82      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.65/1.82          != (k2_struct_0 @ sk_B)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['159', '164'])).
% 1.65/1.82  thf('166', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.82  thf('167', plain,
% 1.65/1.82      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.65/1.82          != (k2_relat_1 @ sk_C)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('demod', [status(thm)], ['165', '166'])).
% 1.65/1.82  thf('168', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.65/1.82      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.65/1.82  thf('169', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.65/1.82      inference('demod', [status(thm)], ['43', '48', '51'])).
% 1.65/1.82  thf('170', plain,
% 1.65/1.82      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.82          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.65/1.82          != (k2_relat_1 @ sk_C)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('demod', [status(thm)], ['167', '168', '169'])).
% 1.65/1.82  thf('171', plain,
% 1.65/1.82      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.82          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['158', '170'])).
% 1.65/1.82  thf('172', plain,
% 1.65/1.82      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.82           (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 1.65/1.82         | ~ (l1_struct_0 @ sk_B)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['157', '171'])).
% 1.65/1.82  thf('173', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.65/1.82      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.82  thf('174', plain, ((l1_struct_0 @ sk_B)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('175', plain,
% 1.65/1.82      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.82          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('demod', [status(thm)], ['172', '173', '174'])).
% 1.65/1.82  thf('176', plain,
% 1.65/1.82      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.65/1.82         <= (~
% 1.65/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82                = (k2_struct_0 @ sk_B))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['156', '175'])).
% 1.65/1.82  thf('177', plain,
% 1.65/1.82      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82          = (k2_struct_0 @ sk_B)))),
% 1.65/1.82      inference('simplify', [status(thm)], ['176'])).
% 1.65/1.82  thf('178', plain,
% 1.65/1.82      (~
% 1.65/1.82       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82          = (k2_struct_0 @ sk_A))) | 
% 1.65/1.82       ~
% 1.65/1.82       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82          = (k2_struct_0 @ sk_B)))),
% 1.65/1.82      inference('split', [status(esa)], ['3'])).
% 1.65/1.82  thf('179', plain,
% 1.65/1.82      (~
% 1.65/1.82       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.65/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.65/1.82          = (k2_struct_0 @ sk_A)))),
% 1.65/1.82      inference('sat_resolution*', [status(thm)], ['177', '178'])).
% 1.65/1.82  thf('180', plain,
% 1.65/1.82      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.65/1.82      inference('simpl_trail', [status(thm)], ['124', '179'])).
% 1.65/1.82  thf('181', plain,
% 1.65/1.82      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.65/1.82        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.82        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.82        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.82      inference('sup-', [status(thm)], ['0', '180'])).
% 1.65/1.82  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.82      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.82  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('184', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('185', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 1.65/1.82      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 1.65/1.82  thf('186', plain, ($false), inference('simplify', [status(thm)], ['185'])).
% 1.65/1.82  
% 1.65/1.82  % SZS output end Refutation
% 1.65/1.82  
% 1.65/1.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
