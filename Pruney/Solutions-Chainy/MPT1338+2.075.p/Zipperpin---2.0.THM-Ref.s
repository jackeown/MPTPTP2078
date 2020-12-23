%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ARELlGSvi3

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:00 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  194 (1455 expanded)
%              Number of leaves         :   38 ( 440 expanded)
%              Depth                    :   23
%              Number of atoms          : 1881 (34853 expanded)
%              Number of equality atoms :  125 (1725 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X14 @ ( k3_relset_1 @ X14 @ X15 @ X16 ) )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k3_relset_1 @ X12 @ X13 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('9',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','17','18'])).

thf('20',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','20','23'])).

thf('25',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','41'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','48'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('50',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

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

thf('60',plain,(
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

thf('61',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('77',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','65','66','77'])).

thf('79',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('81',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('93',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','106'])).

thf('108',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('113',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','113'])).

thf('115',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('116',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','120'])).

thf('122',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','121'])).

thf('123',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['78'])).

thf('124',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('125',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['83'])).

thf('128',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','130'])).

thf('132',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','133'])).

thf('135',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('136',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('139',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X14 @ ( k3_relset_1 @ X14 @ X15 @ X16 ) )
        = ( k2_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('140',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('142',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('145',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','19'])).

thf('146',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('147',plain,
    ( ( k3_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['142','143','144','147'])).

thf('149',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','148'])).

thf('150',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['83'])).

thf('152',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['150','151'])).

thf('153',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['122','152'])).

thf('154',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ARELlGSvi3
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:37:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 254 iterations in 0.081s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.37/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.37/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.55  thf(d3_struct_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf(t62_tops_2, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_struct_0 @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.55                 ( m1_subset_1 @
% 0.37/0.55                   C @ 
% 0.37/0.55                   ( k1_zfmisc_1 @
% 0.37/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.55               ( ( ( ( k2_relset_1 @
% 0.37/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.55                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.55                   ( v2_funct_1 @ C ) ) =>
% 0.37/0.55                 ( ( ( k1_relset_1 @
% 0.37/0.55                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.55                       ( k2_tops_2 @
% 0.37/0.55                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.55                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.55                   ( ( k2_relset_1 @
% 0.37/0.55                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.55                       ( k2_tops_2 @
% 0.37/0.55                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.55                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( l1_struct_0 @ A ) =>
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.55              ( ![C:$i]:
% 0.37/0.55                ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.55                    ( v1_funct_2 @
% 0.37/0.55                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.55                    ( m1_subset_1 @
% 0.37/0.55                      C @ 
% 0.37/0.55                      ( k1_zfmisc_1 @
% 0.37/0.55                        ( k2_zfmisc_1 @
% 0.37/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.55                  ( ( ( ( k2_relset_1 @
% 0.37/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.55                        ( k2_struct_0 @ B ) ) & 
% 0.37/0.55                      ( v2_funct_1 @ C ) ) =>
% 0.37/0.55                    ( ( ( k1_relset_1 @
% 0.37/0.55                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.55                          ( k2_tops_2 @
% 0.37/0.55                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.55                        ( k2_struct_0 @ B ) ) & 
% 0.37/0.55                      ( ( k2_relset_1 @
% 0.37/0.55                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.55                          ( k2_tops_2 @
% 0.37/0.55                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.55                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (((m1_subset_1 @ sk_C @ 
% 0.37/0.55         (k1_zfmisc_1 @ 
% 0.37/0.55          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['0', '1'])).
% 0.37/0.55  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf(t24_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.37/0.55           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.37/0.55         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.37/0.55           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.55         (((k2_relset_1 @ X15 @ X14 @ (k3_relset_1 @ X14 @ X15 @ X16))
% 0.37/0.55            = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.37/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.37/0.55      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf(redefinition_k3_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.55         (((k3_relset_1 @ X12 @ X13 @ X11) = (k4_relat_1 @ X11))
% 0.37/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k4_relat_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d9_funct_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X4 : $i]:
% 0.37/0.55         (~ (v2_funct_1 @ X4)
% 0.37/0.55          | ((k2_funct_1 @ X4) = (k4_relat_1 @ X4))
% 0.37/0.55          | ~ (v1_funct_1 @ X4)
% 0.37/0.55          | ~ (v1_relat_1 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.37/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(cc2_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.55          | (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ 
% 0.37/0.55           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.37/0.55        | (v1_relat_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf(fc6_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.55  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('18', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('19', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['12', '17', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_funct_1 @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['9', '19'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.37/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k1_relat_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['6', '20', '23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (((m1_subset_1 @ sk_C @ 
% 0.37/0.55         (k1_zfmisc_1 @ 
% 0.37/0.55          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.55      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.55  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf(cc5_funct_2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.37/0.55             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.37/0.55          | (v1_partfun1 @ X17 @ X18)
% 0.37/0.55          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.37/0.55          | ~ (v1_funct_1 @ X17)
% 0.37/0.55          | (v1_xboole_0 @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.55  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.55      inference('sup+', [status(thm)], ['33', '38'])).
% 0.37/0.55  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['31', '32', '41'])).
% 0.37/0.55  thf(d4_partfun1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.37/0.55       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i]:
% 0.37/0.55         (~ (v1_partfun1 @ X21 @ X20)
% 0.37/0.55          | ((k1_relat_1 @ X21) = (X20))
% 0.37/0.55          | ~ (v4_relat_1 @ X21 @ X20)
% 0.37/0.55          | ~ (v1_relat_1 @ X21))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.37/0.55        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.55  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf(cc2_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         ((v4_relat_1 @ X5 @ X6)
% 0.37/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.55  thf('48', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['44', '45', '48'])).
% 0.37/0.55  thf(fc5_struct_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.55       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      (![X23 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ (k2_struct_0 @ X23))
% 0.37/0.55          | ~ (l1_struct_0 @ X23)
% 0.37/0.55          | (v2_struct_0 @ X23))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.37/0.55        | (v2_struct_0 @ sk_B)
% 0.37/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.55  thf('52', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.55  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('55', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['24', '55'])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf('58', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['57', '58'])).
% 0.37/0.55  thf(d4_tops_2, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.55       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.37/0.55         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.55         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 0.37/0.55          | ~ (v2_funct_1 @ X26)
% 0.37/0.55          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 0.37/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.37/0.55          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 0.37/0.55          | ~ (v1_funct_1 @ X26))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55            = (k2_funct_1 @ sk_C))
% 0.37/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.55        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55            != (k2_struct_0 @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.55  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('64', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.37/0.55  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('69', plain,
% 0.37/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('70', plain,
% 0.37/0.55      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55          = (k2_struct_0 @ sk_B))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['68', '69'])).
% 0.37/0.55  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55          = (k2_struct_0 @ sk_B))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.55      inference('sup+', [status(thm)], ['67', '72'])).
% 0.37/0.55  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('75', plain,
% 0.37/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['73', '74'])).
% 0.37/0.55  thf('76', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('77', plain,
% 0.37/0.55      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.55  thf('78', plain,
% 0.37/0.55      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55          = (k2_funct_1 @ sk_C))
% 0.37/0.55        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['61', '62', '65', '66', '77'])).
% 0.37/0.55  thf('79', plain,
% 0.37/0.55      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_funct_1 @ sk_C))),
% 0.37/0.55      inference('simplify', [status(thm)], ['78'])).
% 0.37/0.55  thf('80', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('81', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('82', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('83', plain,
% 0.37/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_B))
% 0.37/0.55        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55            != (k2_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('84', plain,
% 0.37/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['83'])).
% 0.37/0.55  thf('85', plain,
% 0.37/0.55      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55           != (k2_struct_0 @ sk_A))
% 0.37/0.55         | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['82', '84'])).
% 0.37/0.55  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('87', plain,
% 0.37/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['85', '86'])).
% 0.37/0.55  thf('88', plain,
% 0.37/0.55      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55           != (k2_struct_0 @ sk_A))
% 0.37/0.55         | ~ (l1_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['81', '87'])).
% 0.37/0.55  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('90', plain,
% 0.37/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['88', '89'])).
% 0.37/0.55  thf('91', plain,
% 0.37/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['80', '90'])).
% 0.37/0.55  thf('92', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('93', plain,
% 0.37/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k1_relat_1 @ sk_C)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['91', '92'])).
% 0.37/0.55  thf('94', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('95', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('96', plain,
% 0.37/0.55      (((m1_subset_1 @ sk_C @ 
% 0.37/0.55         (k1_zfmisc_1 @ 
% 0.37/0.55          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.55      inference('sup+', [status(thm)], ['94', '95'])).
% 0.37/0.55  thf('97', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('98', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['96', '97'])).
% 0.37/0.55  thf('99', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.37/0.55          | (v1_partfun1 @ X17 @ X18)
% 0.37/0.55          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.37/0.55          | ~ (v1_funct_1 @ X17)
% 0.37/0.55          | (v1_xboole_0 @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.37/0.55  thf('100', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['98', '99'])).
% 0.37/0.55  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('102', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('103', plain,
% 0.37/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('104', plain,
% 0.37/0.55      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.55      inference('sup+', [status(thm)], ['102', '103'])).
% 0.37/0.55  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('106', plain,
% 0.37/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['104', '105'])).
% 0.37/0.55  thf('107', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['100', '101', '106'])).
% 0.37/0.55  thf('108', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i]:
% 0.37/0.55         (~ (v1_partfun1 @ X21 @ X20)
% 0.37/0.55          | ((k1_relat_1 @ X21) = (X20))
% 0.37/0.55          | ~ (v4_relat_1 @ X21 @ X20)
% 0.37/0.55          | ~ (v1_relat_1 @ X21))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.37/0.55  thf('109', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.37/0.55        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['107', '108'])).
% 0.37/0.55  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('111', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('112', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         ((v4_relat_1 @ X5 @ X6)
% 0.37/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.55  thf('113', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['111', '112'])).
% 0.37/0.55  thf('114', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.37/0.55        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['109', '110', '113'])).
% 0.37/0.55  thf('115', plain,
% 0.37/0.55      (![X23 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ (k2_struct_0 @ X23))
% 0.37/0.55          | ~ (l1_struct_0 @ X23)
% 0.37/0.55          | (v2_struct_0 @ X23))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.37/0.55  thf('116', plain,
% 0.37/0.55      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.37/0.55        | (v2_struct_0 @ sk_B)
% 0.37/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['114', '115'])).
% 0.37/0.55  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('118', plain,
% 0.37/0.55      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['116', '117'])).
% 0.37/0.55  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('120', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['118', '119'])).
% 0.37/0.55  thf('121', plain,
% 0.37/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k1_relat_1 @ sk_C)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['93', '120'])).
% 0.37/0.55  thf('122', plain,
% 0.37/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['79', '121'])).
% 0.37/0.55  thf('123', plain,
% 0.37/0.55      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_funct_1 @ sk_C))),
% 0.37/0.55      inference('simplify', [status(thm)], ['78'])).
% 0.37/0.55  thf('124', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('125', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('126', plain,
% 0.37/0.55      (![X22 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('127', plain,
% 0.37/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('split', [status(esa)], ['83'])).
% 0.37/0.55  thf('128', plain,
% 0.37/0.55      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55           != (k2_struct_0 @ sk_B))
% 0.37/0.55         | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['126', '127'])).
% 0.37/0.55  thf('129', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('130', plain,
% 0.37/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['128', '129'])).
% 0.37/0.55  thf('131', plain,
% 0.37/0.55      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55           != (k2_struct_0 @ sk_B))
% 0.37/0.55         | ~ (l1_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['125', '130'])).
% 0.37/0.55  thf('132', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('133', plain,
% 0.37/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['131', '132'])).
% 0.37/0.55  thf('134', plain,
% 0.37/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['124', '133'])).
% 0.37/0.55  thf('135', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['118', '119'])).
% 0.37/0.55  thf('136', plain,
% 0.37/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          != (k2_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['134', '135'])).
% 0.37/0.55  thf('137', plain,
% 0.37/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['123', '136'])).
% 0.37/0.55  thf('138', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf('139', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.55         (((k1_relset_1 @ X15 @ X14 @ (k3_relset_1 @ X14 @ X15 @ X16))
% 0.37/0.55            = (k2_relset_1 @ X14 @ X15 @ X16))
% 0.37/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.37/0.55      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.37/0.55  thf('140', plain,
% 0.37/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55         = (k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['138', '139'])).
% 0.37/0.55  thf('141', plain,
% 0.37/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.55  thf('142', plain,
% 0.37/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55         = (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['140', '141'])).
% 0.37/0.55  thf('143', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('144', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('145', plain,
% 0.37/0.55      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_funct_1 @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['9', '19'])).
% 0.37/0.55  thf('146', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.37/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('147', plain,
% 0.37/0.55      (((k3_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.55         = (k2_funct_1 @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['145', '146'])).
% 0.37/0.55  thf('148', plain,
% 0.37/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['142', '143', '144', '147'])).
% 0.37/0.55  thf('149', plain,
% 0.37/0.55      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55                = (k2_struct_0 @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['137', '148'])).
% 0.37/0.55  thf('150', plain,
% 0.37/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          = (k2_struct_0 @ sk_B)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['149'])).
% 0.37/0.55  thf('151', plain,
% 0.37/0.55      (~
% 0.37/0.55       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          = (k2_struct_0 @ sk_A))) | 
% 0.37/0.55       ~
% 0.37/0.55       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          = (k2_struct_0 @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['83'])).
% 0.37/0.55  thf('152', plain,
% 0.37/0.55      (~
% 0.37/0.55       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.55          = (k2_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['150', '151'])).
% 0.37/0.55  thf('153', plain,
% 0.37/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.37/0.55         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['122', '152'])).
% 0.37/0.55  thf('154', plain, ($false),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['56', '153'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
