%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LbNeYdhUgx

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:00 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  203 (2099 expanded)
%              Number of leaves         :   41 ( 630 expanded)
%              Depth                    :   22
%              Number of atoms          : 1762 (50783 expanded)
%              Number of equality atoms :  119 (2570 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_relset_1 @ X19 @ X20 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('5',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['5','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','16'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('41',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','46'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('56',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','53','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['17','59'])).

thf('61',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('62',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','53','58'])).

thf('70',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','53','58'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('72',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','46'])).

thf('85',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('92',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('93',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('95',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['82','95'])).

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

thf('97',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','93','94'])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['114','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','93','94'])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','99','112','113','127'])).

thf('129',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','93','94'])).

thf('131',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','129','130'])).

thf('132',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('134',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('136',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('141',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','53','58'])).

thf('143',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','53','58'])).

thf('144',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_tops_2 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','144'])).

thf('146',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['17','59'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('147',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('148',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('150',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('151',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','153'])).

thf('155',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','154'])).

thf('156',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('158',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['156','157'])).

thf('159',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['131','158'])).

thf('160',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LbNeYdhUgx
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:55:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.35/1.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.35/1.53  % Solved by: fo/fo7.sh
% 1.35/1.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.53  % done 389 iterations in 1.090s
% 1.35/1.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.35/1.53  % SZS output start Refutation
% 1.35/1.53  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.35/1.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.35/1.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.35/1.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.35/1.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.35/1.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.35/1.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.35/1.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.35/1.53  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.53  thf(sk_C_type, type, sk_C: $i).
% 1.35/1.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.53  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.35/1.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.35/1.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.35/1.53  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.35/1.53  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 1.35/1.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.35/1.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.35/1.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.35/1.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.35/1.53  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.35/1.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.35/1.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.35/1.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.35/1.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.35/1.53  thf(t62_tops_2, conjecture,
% 1.35/1.53    (![A:$i]:
% 1.35/1.53     ( ( l1_struct_0 @ A ) =>
% 1.35/1.53       ( ![B:$i]:
% 1.35/1.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.35/1.53           ( ![C:$i]:
% 1.35/1.53             ( ( ( v1_funct_1 @ C ) & 
% 1.35/1.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.35/1.53                 ( m1_subset_1 @
% 1.35/1.53                   C @ 
% 1.35/1.53                   ( k1_zfmisc_1 @
% 1.35/1.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.35/1.53               ( ( ( ( k2_relset_1 @
% 1.35/1.53                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.35/1.53                     ( k2_struct_0 @ B ) ) & 
% 1.35/1.53                   ( v2_funct_1 @ C ) ) =>
% 1.35/1.53                 ( ( ( k1_relset_1 @
% 1.35/1.53                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.35/1.53                       ( k2_tops_2 @
% 1.35/1.53                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.35/1.53                     ( k2_struct_0 @ B ) ) & 
% 1.35/1.53                   ( ( k2_relset_1 @
% 1.35/1.53                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.35/1.53                       ( k2_tops_2 @
% 1.35/1.53                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.35/1.53                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.35/1.53  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.53    (~( ![A:$i]:
% 1.35/1.53        ( ( l1_struct_0 @ A ) =>
% 1.35/1.53          ( ![B:$i]:
% 1.35/1.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.35/1.53              ( ![C:$i]:
% 1.35/1.53                ( ( ( v1_funct_1 @ C ) & 
% 1.35/1.53                    ( v1_funct_2 @
% 1.35/1.53                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.35/1.53                    ( m1_subset_1 @
% 1.35/1.53                      C @ 
% 1.35/1.53                      ( k1_zfmisc_1 @
% 1.35/1.53                        ( k2_zfmisc_1 @
% 1.35/1.53                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.35/1.53                  ( ( ( ( k2_relset_1 @
% 1.35/1.53                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.35/1.53                        ( k2_struct_0 @ B ) ) & 
% 1.35/1.53                      ( v2_funct_1 @ C ) ) =>
% 1.35/1.53                    ( ( ( k1_relset_1 @
% 1.35/1.53                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.35/1.53                          ( k2_tops_2 @
% 1.35/1.53                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.35/1.53                        ( k2_struct_0 @ B ) ) & 
% 1.35/1.53                      ( ( k2_relset_1 @
% 1.35/1.53                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.35/1.53                          ( k2_tops_2 @
% 1.35/1.53                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.35/1.53                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.35/1.53    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.35/1.53  thf('0', plain,
% 1.35/1.53      ((m1_subset_1 @ sk_C @ 
% 1.35/1.53        (k1_zfmisc_1 @ 
% 1.35/1.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf(dt_k3_relset_1, axiom,
% 1.35/1.53    (![A:$i,B:$i,C:$i]:
% 1.35/1.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.53       ( m1_subset_1 @
% 1.35/1.53         ( k3_relset_1 @ A @ B @ C ) @ 
% 1.35/1.53         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 1.35/1.53  thf('1', plain,
% 1.35/1.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.35/1.53         ((m1_subset_1 @ (k3_relset_1 @ X9 @ X10 @ X11) @ 
% 1.35/1.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 1.35/1.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.35/1.53      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 1.35/1.53  thf('2', plain,
% 1.35/1.53      ((m1_subset_1 @ 
% 1.35/1.53        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.35/1.53        (k1_zfmisc_1 @ 
% 1.35/1.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.35/1.53      inference('sup-', [status(thm)], ['0', '1'])).
% 1.35/1.53  thf('3', plain,
% 1.35/1.53      ((m1_subset_1 @ sk_C @ 
% 1.35/1.53        (k1_zfmisc_1 @ 
% 1.35/1.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf(redefinition_k3_relset_1, axiom,
% 1.35/1.53    (![A:$i,B:$i,C:$i]:
% 1.35/1.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.53       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 1.35/1.53  thf('4', plain,
% 1.35/1.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.35/1.53         (((k3_relset_1 @ X19 @ X20 @ X18) = (k4_relat_1 @ X18))
% 1.35/1.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.35/1.53      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 1.35/1.53  thf('5', plain,
% 1.35/1.53      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.35/1.53         = (k4_relat_1 @ sk_C))),
% 1.35/1.53      inference('sup-', [status(thm)], ['3', '4'])).
% 1.35/1.53  thf('6', plain,
% 1.35/1.53      ((m1_subset_1 @ sk_C @ 
% 1.35/1.53        (k1_zfmisc_1 @ 
% 1.35/1.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf(cc2_relat_1, axiom,
% 1.35/1.53    (![A:$i]:
% 1.35/1.53     ( ( v1_relat_1 @ A ) =>
% 1.35/1.53       ( ![B:$i]:
% 1.35/1.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.35/1.53  thf('7', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.35/1.53          | (v1_relat_1 @ X0)
% 1.35/1.53          | ~ (v1_relat_1 @ X1))),
% 1.35/1.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.35/1.53  thf('8', plain,
% 1.35/1.53      ((~ (v1_relat_1 @ 
% 1.35/1.53           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.35/1.53        | (v1_relat_1 @ sk_C))),
% 1.35/1.53      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.53  thf(fc6_relat_1, axiom,
% 1.35/1.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.35/1.53  thf('9', plain,
% 1.35/1.53      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.35/1.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.35/1.53  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.53      inference('demod', [status(thm)], ['8', '9'])).
% 1.35/1.53  thf(d9_funct_1, axiom,
% 1.35/1.53    (![A:$i]:
% 1.35/1.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.53       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.35/1.53  thf('11', plain,
% 1.35/1.53      (![X5 : $i]:
% 1.35/1.53         (~ (v2_funct_1 @ X5)
% 1.35/1.53          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 1.35/1.53          | ~ (v1_funct_1 @ X5)
% 1.35/1.53          | ~ (v1_relat_1 @ X5))),
% 1.35/1.53      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.35/1.53  thf('12', plain,
% 1.35/1.53      ((~ (v1_funct_1 @ sk_C)
% 1.35/1.53        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.35/1.53        | ~ (v2_funct_1 @ sk_C))),
% 1.35/1.53      inference('sup-', [status(thm)], ['10', '11'])).
% 1.35/1.53  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('14', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('15', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.35/1.53      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.35/1.53  thf('16', plain,
% 1.35/1.53      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.35/1.53         = (k2_funct_1 @ sk_C))),
% 1.35/1.53      inference('demod', [status(thm)], ['5', '15'])).
% 1.35/1.53  thf('17', plain,
% 1.35/1.53      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.35/1.53        (k1_zfmisc_1 @ 
% 1.35/1.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.35/1.53      inference('demod', [status(thm)], ['2', '16'])).
% 1.35/1.53  thf(d3_struct_0, axiom,
% 1.35/1.53    (![A:$i]:
% 1.35/1.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.35/1.53  thf('18', plain,
% 1.35/1.53      (![X26 : $i]:
% 1.35/1.53         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.53  thf('19', plain,
% 1.35/1.53      ((m1_subset_1 @ sk_C @ 
% 1.35/1.53        (k1_zfmisc_1 @ 
% 1.35/1.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('20', plain,
% 1.35/1.53      (((m1_subset_1 @ sk_C @ 
% 1.35/1.53         (k1_zfmisc_1 @ 
% 1.35/1.53          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.35/1.53        | ~ (l1_struct_0 @ sk_B))),
% 1.35/1.53      inference('sup+', [status(thm)], ['18', '19'])).
% 1.35/1.53  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('22', plain,
% 1.35/1.53      ((m1_subset_1 @ sk_C @ 
% 1.35/1.53        (k1_zfmisc_1 @ 
% 1.35/1.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.35/1.53      inference('demod', [status(thm)], ['20', '21'])).
% 1.35/1.53  thf('23', plain,
% 1.35/1.53      ((m1_subset_1 @ sk_C @ 
% 1.35/1.53        (k1_zfmisc_1 @ 
% 1.35/1.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf(redefinition_k2_relset_1, axiom,
% 1.35/1.53    (![A:$i,B:$i,C:$i]:
% 1.35/1.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.35/1.53  thf('24', plain,
% 1.35/1.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.35/1.53         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.35/1.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.35/1.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.35/1.53  thf('25', plain,
% 1.35/1.53      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.35/1.53         = (k2_relat_1 @ sk_C))),
% 1.35/1.53      inference('sup-', [status(thm)], ['23', '24'])).
% 1.35/1.53  thf('26', plain,
% 1.35/1.53      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.35/1.53         = (k2_struct_0 @ sk_B))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.53      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.53  thf('28', plain,
% 1.35/1.53      ((m1_subset_1 @ sk_C @ 
% 1.35/1.53        (k1_zfmisc_1 @ 
% 1.35/1.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.35/1.53      inference('demod', [status(thm)], ['22', '27'])).
% 1.35/1.53  thf(cc5_funct_2, axiom,
% 1.35/1.53    (![A:$i,B:$i]:
% 1.35/1.53     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.35/1.53       ( ![C:$i]:
% 1.35/1.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.53           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.35/1.53             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.35/1.53  thf('29', plain,
% 1.35/1.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.35/1.53         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.35/1.53          | (v1_partfun1 @ X21 @ X22)
% 1.35/1.53          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 1.35/1.53          | ~ (v1_funct_1 @ X21)
% 1.35/1.53          | (v1_xboole_0 @ X23))),
% 1.35/1.53      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.35/1.53  thf('30', plain,
% 1.35/1.53      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.35/1.53        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.54        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.35/1.54        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['28', '29'])).
% 1.35/1.54  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('32', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('33', plain,
% 1.35/1.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('34', plain,
% 1.35/1.54      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.35/1.54        | ~ (l1_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['32', '33'])).
% 1.35/1.54  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('36', plain,
% 1.35/1.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('demod', [status(thm)], ['34', '35'])).
% 1.35/1.54  thf('37', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.54  thf('38', plain,
% 1.35/1.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.35/1.54      inference('demod', [status(thm)], ['36', '37'])).
% 1.35/1.54  thf('39', plain,
% 1.35/1.54      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.35/1.54        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('demod', [status(thm)], ['30', '31', '38'])).
% 1.35/1.54  thf('40', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.54  thf(fc5_struct_0, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.35/1.54       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.35/1.54  thf('41', plain,
% 1.35/1.54      (![X27 : $i]:
% 1.35/1.54         (~ (v1_xboole_0 @ (k2_struct_0 @ X27))
% 1.35/1.54          | ~ (l1_struct_0 @ X27)
% 1.35/1.54          | (v2_struct_0 @ X27))),
% 1.35/1.54      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.35/1.54  thf('42', plain,
% 1.35/1.54      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.35/1.54        | (v2_struct_0 @ sk_B)
% 1.35/1.54        | ~ (l1_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup-', [status(thm)], ['40', '41'])).
% 1.35/1.54  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('44', plain,
% 1.35/1.54      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.35/1.54      inference('demod', [status(thm)], ['42', '43'])).
% 1.35/1.54  thf('45', plain, (~ (v2_struct_0 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('46', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.35/1.54      inference('clc', [status(thm)], ['44', '45'])).
% 1.35/1.54  thf('47', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('clc', [status(thm)], ['39', '46'])).
% 1.35/1.54  thf(d4_partfun1, axiom,
% 1.35/1.54    (![A:$i,B:$i]:
% 1.35/1.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.35/1.54       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.35/1.54  thf('48', plain,
% 1.35/1.54      (![X24 : $i, X25 : $i]:
% 1.35/1.54         (~ (v1_partfun1 @ X25 @ X24)
% 1.35/1.54          | ((k1_relat_1 @ X25) = (X24))
% 1.35/1.54          | ~ (v4_relat_1 @ X25 @ X24)
% 1.35/1.54          | ~ (v1_relat_1 @ X25))),
% 1.35/1.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.35/1.54  thf('49', plain,
% 1.35/1.54      ((~ (v1_relat_1 @ sk_C)
% 1.35/1.54        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.35/1.54        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['47', '48'])).
% 1.35/1.54  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.54      inference('demod', [status(thm)], ['8', '9'])).
% 1.35/1.54  thf('51', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_C @ 
% 1.35/1.54        (k1_zfmisc_1 @ 
% 1.35/1.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf(cc2_relset_1, axiom,
% 1.35/1.54    (![A:$i,B:$i,C:$i]:
% 1.35/1.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.35/1.54  thf('52', plain,
% 1.35/1.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.35/1.54         ((v4_relat_1 @ X6 @ X7)
% 1.35/1.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.35/1.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.35/1.54  thf('53', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('sup-', [status(thm)], ['51', '52'])).
% 1.35/1.54  thf('54', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.35/1.54      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.35/1.54  thf(t37_relat_1, axiom,
% 1.35/1.54    (![A:$i]:
% 1.35/1.54     ( ( v1_relat_1 @ A ) =>
% 1.35/1.54       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.35/1.54         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.35/1.54  thf('55', plain,
% 1.35/1.54      (![X4 : $i]:
% 1.35/1.54         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 1.35/1.54          | ~ (v1_relat_1 @ X4))),
% 1.35/1.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.35/1.54  thf('56', plain,
% 1.35/1.54      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.35/1.54        | ~ (v1_relat_1 @ sk_C))),
% 1.35/1.54      inference('sup+', [status(thm)], ['54', '55'])).
% 1.35/1.54  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.54      inference('demod', [status(thm)], ['8', '9'])).
% 1.35/1.54  thf('58', plain,
% 1.35/1.54      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.54      inference('demod', [status(thm)], ['56', '57'])).
% 1.35/1.54  thf('59', plain,
% 1.35/1.54      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['49', '50', '53', '58'])).
% 1.35/1.54  thf('60', plain,
% 1.35/1.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.35/1.54        (k1_zfmisc_1 @ 
% 1.35/1.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 1.35/1.54          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.35/1.54      inference('demod', [status(thm)], ['17', '59'])).
% 1.35/1.54  thf('61', plain,
% 1.35/1.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.35/1.54         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.35/1.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.35/1.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.35/1.54  thf('62', plain,
% 1.35/1.54      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.35/1.54         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 1.35/1.54         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['60', '61'])).
% 1.35/1.54  thf('63', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('64', plain,
% 1.35/1.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54          != (k2_struct_0 @ sk_B))
% 1.35/1.54        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54            != (k2_struct_0 @ sk_A)))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('65', plain,
% 1.35/1.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54          != (k2_struct_0 @ sk_A)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_A))))),
% 1.35/1.54      inference('split', [status(esa)], ['64'])).
% 1.35/1.54  thf('66', plain,
% 1.35/1.54      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54           != (k2_struct_0 @ sk_A))
% 1.35/1.54         | ~ (l1_struct_0 @ sk_B)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_A))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['63', '65'])).
% 1.35/1.54  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('68', plain,
% 1.35/1.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54          != (k2_struct_0 @ sk_A)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_A))))),
% 1.35/1.54      inference('demod', [status(thm)], ['66', '67'])).
% 1.35/1.54  thf('69', plain,
% 1.35/1.54      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['49', '50', '53', '58'])).
% 1.35/1.54  thf('70', plain,
% 1.35/1.54      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['49', '50', '53', '58'])).
% 1.35/1.54  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.54  thf('72', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('73', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('74', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_C @ 
% 1.35/1.54        (k1_zfmisc_1 @ 
% 1.35/1.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('75', plain,
% 1.35/1.54      (((m1_subset_1 @ sk_C @ 
% 1.35/1.54         (k1_zfmisc_1 @ 
% 1.35/1.54          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.35/1.54        | ~ (l1_struct_0 @ sk_A))),
% 1.35/1.54      inference('sup+', [status(thm)], ['73', '74'])).
% 1.35/1.54  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('77', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_C @ 
% 1.35/1.54        (k1_zfmisc_1 @ 
% 1.35/1.54         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.35/1.54      inference('demod', [status(thm)], ['75', '76'])).
% 1.35/1.54  thf('78', plain,
% 1.35/1.54      (((m1_subset_1 @ sk_C @ 
% 1.35/1.54         (k1_zfmisc_1 @ 
% 1.35/1.54          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.35/1.54        | ~ (l1_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['72', '77'])).
% 1.35/1.54  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('80', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_C @ 
% 1.35/1.54        (k1_zfmisc_1 @ 
% 1.35/1.54         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.35/1.54      inference('demod', [status(thm)], ['78', '79'])).
% 1.35/1.54  thf('81', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.54  thf('82', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_C @ 
% 1.35/1.54        (k1_zfmisc_1 @ 
% 1.35/1.54         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.35/1.54      inference('demod', [status(thm)], ['80', '81'])).
% 1.35/1.54  thf('83', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('84', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('clc', [status(thm)], ['39', '46'])).
% 1.35/1.54  thf('85', plain,
% 1.35/1.54      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.35/1.54      inference('sup+', [status(thm)], ['83', '84'])).
% 1.35/1.54  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('87', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['85', '86'])).
% 1.35/1.54  thf('88', plain,
% 1.35/1.54      (![X24 : $i, X25 : $i]:
% 1.35/1.54         (~ (v1_partfun1 @ X25 @ X24)
% 1.35/1.54          | ((k1_relat_1 @ X25) = (X24))
% 1.35/1.54          | ~ (v4_relat_1 @ X25 @ X24)
% 1.35/1.54          | ~ (v1_relat_1 @ X25))),
% 1.35/1.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.35/1.54  thf('89', plain,
% 1.35/1.54      ((~ (v1_relat_1 @ sk_C)
% 1.35/1.54        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.35/1.54        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['87', '88'])).
% 1.35/1.54  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.54      inference('demod', [status(thm)], ['8', '9'])).
% 1.35/1.54  thf('91', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_C @ 
% 1.35/1.54        (k1_zfmisc_1 @ 
% 1.35/1.54         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.35/1.54      inference('demod', [status(thm)], ['75', '76'])).
% 1.35/1.54  thf('92', plain,
% 1.35/1.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.35/1.54         ((v4_relat_1 @ X6 @ X7)
% 1.35/1.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.35/1.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.35/1.54  thf('93', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.35/1.54      inference('sup-', [status(thm)], ['91', '92'])).
% 1.35/1.54  thf('94', plain,
% 1.35/1.54      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.54      inference('demod', [status(thm)], ['56', '57'])).
% 1.35/1.54  thf('95', plain,
% 1.35/1.54      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['89', '90', '93', '94'])).
% 1.35/1.54  thf('96', plain,
% 1.35/1.54      ((m1_subset_1 @ sk_C @ 
% 1.35/1.54        (k1_zfmisc_1 @ 
% 1.35/1.54         (k2_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54          (k2_relat_1 @ sk_C))))),
% 1.35/1.54      inference('demod', [status(thm)], ['82', '95'])).
% 1.35/1.54  thf(d4_tops_2, axiom,
% 1.35/1.54    (![A:$i,B:$i,C:$i]:
% 1.35/1.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.35/1.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.54       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.35/1.54         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.35/1.54  thf('97', plain,
% 1.35/1.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.35/1.54         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 1.35/1.54          | ~ (v2_funct_1 @ X30)
% 1.35/1.54          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 1.35/1.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.35/1.54          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 1.35/1.54          | ~ (v1_funct_1 @ X30))),
% 1.35/1.54      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.35/1.54  thf('98', plain,
% 1.35/1.54      ((~ (v1_funct_1 @ sk_C)
% 1.35/1.54        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54             (k2_relat_1 @ sk_C))
% 1.35/1.54        | ((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54            (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))
% 1.35/1.54        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.54        | ((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54            (k2_relat_1 @ sk_C) @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['96', '97'])).
% 1.35/1.54  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('100', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('101', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('102', plain,
% 1.35/1.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('103', plain,
% 1.35/1.54      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.35/1.54        | ~ (l1_struct_0 @ sk_A))),
% 1.35/1.54      inference('sup+', [status(thm)], ['101', '102'])).
% 1.35/1.54  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('105', plain,
% 1.35/1.54      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.35/1.54      inference('demod', [status(thm)], ['103', '104'])).
% 1.35/1.54  thf('106', plain,
% 1.35/1.54      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.35/1.54        | ~ (l1_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['100', '105'])).
% 1.35/1.54  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('108', plain,
% 1.35/1.54      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('demod', [status(thm)], ['106', '107'])).
% 1.35/1.54  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.54  thf('110', plain,
% 1.35/1.54      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.35/1.54      inference('demod', [status(thm)], ['108', '109'])).
% 1.35/1.54  thf('111', plain,
% 1.35/1.54      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['89', '90', '93', '94'])).
% 1.35/1.54  thf('112', plain,
% 1.35/1.54      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54        (k2_relat_1 @ sk_C))),
% 1.35/1.54      inference('demod', [status(thm)], ['110', '111'])).
% 1.35/1.54  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('114', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('115', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('116', plain,
% 1.35/1.54      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.35/1.54         = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('117', plain,
% 1.35/1.54      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.35/1.54          = (k2_struct_0 @ sk_B))
% 1.35/1.54        | ~ (l1_struct_0 @ sk_A))),
% 1.35/1.54      inference('sup+', [status(thm)], ['115', '116'])).
% 1.35/1.54  thf('118', plain, ((l1_struct_0 @ sk_A)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('119', plain,
% 1.35/1.54      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.35/1.54         = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('demod', [status(thm)], ['117', '118'])).
% 1.35/1.54  thf('120', plain,
% 1.35/1.54      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.35/1.54          = (k2_struct_0 @ sk_B))
% 1.35/1.54        | ~ (l1_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['114', '119'])).
% 1.35/1.54  thf('121', plain, ((l1_struct_0 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('122', plain,
% 1.35/1.54      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.35/1.54         = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('demod', [status(thm)], ['120', '121'])).
% 1.35/1.54  thf('123', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.54  thf('124', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.54  thf('125', plain,
% 1.35/1.54      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.35/1.54         = (k2_relat_1 @ sk_C))),
% 1.35/1.54      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.35/1.54  thf('126', plain,
% 1.35/1.54      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['89', '90', '93', '94'])).
% 1.35/1.54  thf('127', plain,
% 1.35/1.54      (((k2_relset_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54         (k2_relat_1 @ sk_C) @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.35/1.54      inference('demod', [status(thm)], ['125', '126'])).
% 1.35/1.54  thf('128', plain,
% 1.35/1.54      ((((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54          (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))
% 1.35/1.54        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.35/1.54      inference('demod', [status(thm)], ['98', '99', '112', '113', '127'])).
% 1.35/1.54  thf('129', plain,
% 1.35/1.54      (((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54         (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.35/1.54      inference('simplify', [status(thm)], ['128'])).
% 1.35/1.54  thf('130', plain,
% 1.35/1.54      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['89', '90', '93', '94'])).
% 1.35/1.54  thf('131', plain,
% 1.35/1.54      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.35/1.54          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 1.35/1.54          != (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_A))))),
% 1.35/1.54      inference('demod', [status(thm)], ['68', '69', '70', '71', '129', '130'])).
% 1.35/1.54  thf('132', plain,
% 1.35/1.54      (((k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54         (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.35/1.54      inference('simplify', [status(thm)], ['128'])).
% 1.35/1.54  thf('133', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.54  thf('134', plain,
% 1.35/1.54      (![X26 : $i]:
% 1.35/1.54         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 1.35/1.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.35/1.54  thf('135', plain,
% 1.35/1.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54          != (k2_struct_0 @ sk_B)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_B))))),
% 1.35/1.54      inference('split', [status(esa)], ['64'])).
% 1.35/1.54  thf('136', plain,
% 1.35/1.54      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54           != (k2_struct_0 @ sk_B))
% 1.35/1.54         | ~ (l1_struct_0 @ sk_B)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_B))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['134', '135'])).
% 1.35/1.54  thf('137', plain, ((l1_struct_0 @ sk_B)),
% 1.35/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.54  thf('138', plain,
% 1.35/1.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54          != (k2_struct_0 @ sk_B)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_B))))),
% 1.35/1.54      inference('demod', [status(thm)], ['136', '137'])).
% 1.35/1.54  thf('139', plain,
% 1.35/1.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.35/1.54          != (k2_struct_0 @ sk_B)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_B))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['133', '138'])).
% 1.35/1.54  thf('140', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.35/1.54      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.54  thf('141', plain,
% 1.35/1.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.35/1.54          != (k2_relat_1 @ sk_C)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_B))))),
% 1.35/1.54      inference('demod', [status(thm)], ['139', '140'])).
% 1.35/1.54  thf('142', plain,
% 1.35/1.54      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['49', '50', '53', '58'])).
% 1.35/1.54  thf('143', plain,
% 1.35/1.54      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 1.35/1.54      inference('demod', [status(thm)], ['49', '50', '53', '58'])).
% 1.35/1.54  thf('144', plain,
% 1.35/1.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.35/1.54          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54          (k2_tops_2 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.35/1.54           (k2_relat_1 @ sk_C) @ sk_C))
% 1.35/1.54          != (k2_relat_1 @ sk_C)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_B))))),
% 1.35/1.54      inference('demod', [status(thm)], ['141', '142', '143'])).
% 1.35/1.54  thf('145', plain,
% 1.35/1.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.35/1.54          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 1.35/1.54          != (k2_relat_1 @ sk_C)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_B))))),
% 1.35/1.54      inference('sup-', [status(thm)], ['132', '144'])).
% 1.35/1.54  thf('146', plain,
% 1.35/1.54      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.35/1.54        (k1_zfmisc_1 @ 
% 1.35/1.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 1.35/1.54          (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.35/1.54      inference('demod', [status(thm)], ['17', '59'])).
% 1.35/1.54  thf(redefinition_k1_relset_1, axiom,
% 1.35/1.54    (![A:$i,B:$i,C:$i]:
% 1.35/1.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.35/1.54  thf('147', plain,
% 1.35/1.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.35/1.54         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.35/1.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.35/1.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.35/1.54  thf('148', plain,
% 1.35/1.54      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.35/1.54         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 1.35/1.54         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.54      inference('sup-', [status(thm)], ['146', '147'])).
% 1.35/1.54  thf('149', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.35/1.54      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.35/1.54  thf('150', plain,
% 1.35/1.54      (![X4 : $i]:
% 1.35/1.54         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 1.35/1.54          | ~ (v1_relat_1 @ X4))),
% 1.35/1.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.35/1.54  thf('151', plain,
% 1.35/1.54      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.35/1.54        | ~ (v1_relat_1 @ sk_C))),
% 1.35/1.54      inference('sup+', [status(thm)], ['149', '150'])).
% 1.35/1.54  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.54      inference('demod', [status(thm)], ['8', '9'])).
% 1.35/1.54  thf('153', plain,
% 1.35/1.54      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.54      inference('demod', [status(thm)], ['151', '152'])).
% 1.35/1.54  thf('154', plain,
% 1.35/1.54      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.35/1.54         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 1.35/1.54         = (k2_relat_1 @ sk_C))),
% 1.35/1.54      inference('demod', [status(thm)], ['148', '153'])).
% 1.35/1.54  thf('155', plain,
% 1.35/1.54      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.35/1.54         <= (~
% 1.35/1.54             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54                = (k2_struct_0 @ sk_B))))),
% 1.35/1.54      inference('demod', [status(thm)], ['145', '154'])).
% 1.35/1.54  thf('156', plain,
% 1.35/1.54      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54          = (k2_struct_0 @ sk_B)))),
% 1.35/1.54      inference('simplify', [status(thm)], ['155'])).
% 1.35/1.54  thf('157', plain,
% 1.35/1.54      (~
% 1.35/1.54       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54          = (k2_struct_0 @ sk_A))) | 
% 1.35/1.54       ~
% 1.35/1.54       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54          = (k2_struct_0 @ sk_B)))),
% 1.35/1.54      inference('split', [status(esa)], ['64'])).
% 1.35/1.54  thf('158', plain,
% 1.35/1.54      (~
% 1.35/1.54       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.35/1.54          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.35/1.54          = (k2_struct_0 @ sk_A)))),
% 1.35/1.54      inference('sat_resolution*', [status(thm)], ['156', '157'])).
% 1.35/1.54  thf('159', plain,
% 1.35/1.54      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 1.35/1.54         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 1.35/1.54         != (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.54      inference('simpl_trail', [status(thm)], ['131', '158'])).
% 1.35/1.54  thf('160', plain, ($false),
% 1.35/1.54      inference('simplify_reflect-', [status(thm)], ['62', '159'])).
% 1.35/1.54  
% 1.35/1.54  % SZS output end Refutation
% 1.35/1.54  
% 1.35/1.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
