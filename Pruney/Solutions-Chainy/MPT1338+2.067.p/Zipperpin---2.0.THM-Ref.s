%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.StGbcHEAN9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:58 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  307 (2837 expanded)
%              Number of leaves         :   54 ( 835 expanded)
%              Depth                    :   30
%              Number of atoms          : 2878 (71324 expanded)
%              Number of equality atoms :  180 (3599 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
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
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( v1_partfun1 @ X38 @ X39 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X47: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('37',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_partfun1 @ X42 @ X41 )
      | ( ( k1_relat_1 @ X42 )
        = X41 )
      | ~ ( v4_relat_1 @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('49',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('57',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_partfun1 @ X42 @ X41 )
      | ( ( k1_relat_1 @ X42 )
        = X41 )
      | ~ ( v4_relat_1 @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('64',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','66'])).

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

thf('68',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k2_relset_1 @ X49 @ X48 @ X50 )
       != X48 )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_tops_2 @ X49 @ X48 @ X50 )
        = ( k2_funct_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('80',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('81',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','77','78','83'])).

thf('85',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('92',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

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

thf('99',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X45 @ X44 @ X43 )
       != X44 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('104',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('112',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('122',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('124',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','101','110','124','125'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('129',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('130',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('131',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k10_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X15 ) @ X16 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('132',plain,(
    ! [X10: $i] :
      ( ( ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('137',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('139',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('140',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('142',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k8_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k10_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','143'])).

thf('145',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['135','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('151',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('153',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('154',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t51_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) )
              & ( v2_funct_1 @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('155',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X17 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) )
       != ( k2_relat_1 @ X18 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('157',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['153','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['152','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('164',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['151','165'])).

thf('167',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('170',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','170'])).

thf('172',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('173',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','10','47','48','89','171','172'])).

thf('174',plain,
    ( $false
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('176',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('177',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('178',plain,(
    ! [X14: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('179',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','66'])).

thf('181',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X45 @ X44 @ X43 )
       != X44 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('182',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('185',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('188',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['179','188'])).

thf('190',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('191',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('195',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('196',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['194','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['193','199'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['200','201','202','203'])).

thf('205',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['178','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('207',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['205','206','207','208'])).

thf('210',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('211',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['209','212'])).

thf('214',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('215',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('218',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['213','214','215','216','217'])).

thf('219',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','218'])).

thf('220',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('221',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('222',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k2_relset_1 @ X49 @ X48 @ X50 )
       != X48 )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_tops_2 @ X49 @ X48 @ X50 )
        = ( k2_funct_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('223',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('226',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('228',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['223','224','225','226','227'])).

thf('229',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('231',plain,(
    ! [X46: $i] :
      ( ( ( k2_struct_0 @ X46 )
        = ( u1_struct_0 @ X46 ) )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('232',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('233',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['230','235'])).

thf('237',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('238',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('240',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('241',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['229','241'])).

thf('243',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['220','242'])).

thf('244',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('245',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','246'])).

thf('248',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('250',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['248','249'])).

thf('251',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['174','250'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.StGbcHEAN9
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:11 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.46/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.71  % Solved by: fo/fo7.sh
% 0.46/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.71  % done 503 iterations in 0.270s
% 0.46/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.71  % SZS output start Refutation
% 0.46/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.71  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.71  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.71  thf(d3_struct_0, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.71  thf('0', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf(t62_tops_2, conjecture,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_struct_0 @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.71           ( ![C:$i]:
% 0.46/0.71             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.71                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.71                 ( m1_subset_1 @
% 0.46/0.71                   C @ 
% 0.46/0.71                   ( k1_zfmisc_1 @
% 0.46/0.71                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.71               ( ( ( ( k2_relset_1 @
% 0.46/0.71                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.71                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.71                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.71                 ( ( ( k1_relset_1 @
% 0.46/0.71                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.71                       ( k2_tops_2 @
% 0.46/0.71                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.46/0.71                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.71                   ( ( k2_relset_1 @
% 0.46/0.71                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.71                       ( k2_tops_2 @
% 0.46/0.71                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.46/0.71                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.71    (~( ![A:$i]:
% 0.46/0.71        ( ( l1_struct_0 @ A ) =>
% 0.46/0.71          ( ![B:$i]:
% 0.46/0.71            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.71              ( ![C:$i]:
% 0.46/0.71                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.71                    ( v1_funct_2 @
% 0.46/0.71                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.71                    ( m1_subset_1 @
% 0.46/0.71                      C @ 
% 0.46/0.71                      ( k1_zfmisc_1 @
% 0.46/0.71                        ( k2_zfmisc_1 @
% 0.46/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.71                  ( ( ( ( k2_relset_1 @
% 0.46/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.71                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.71                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.71                    ( ( ( k1_relset_1 @
% 0.46/0.71                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.71                          ( k2_tops_2 @
% 0.46/0.71                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.46/0.71                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.71                      ( ( k2_relset_1 @
% 0.46/0.71                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.71                          ( k2_tops_2 @
% 0.46/0.71                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.46/0.71                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.46/0.71    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.46/0.71  thf('1', plain,
% 0.46/0.71      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71          != (k2_struct_0 @ sk_B))
% 0.46/0.71        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71            != (k2_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('2', plain,
% 0.46/0.71      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71          != (k2_struct_0 @ sk_A)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_A))))),
% 0.46/0.71      inference('split', [status(esa)], ['1'])).
% 0.46/0.71  thf('3', plain,
% 0.46/0.71      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71           != (k2_struct_0 @ sk_A))
% 0.46/0.71         | ~ (l1_struct_0 @ sk_B)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_A))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['0', '2'])).
% 0.46/0.71  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('5', plain,
% 0.46/0.71      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71          != (k2_struct_0 @ sk_A)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_A))))),
% 0.46/0.71      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.71  thf('6', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.71  thf('7', plain,
% 0.46/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.71         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.46/0.71          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.71  thf('8', plain,
% 0.46/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71         = (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.71  thf('9', plain,
% 0.46/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71         = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('10', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('11', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('12', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('13', plain,
% 0.46/0.71      (((m1_subset_1 @ sk_C @ 
% 0.46/0.71         (k1_zfmisc_1 @ 
% 0.46/0.71          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.71  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('15', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.71  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('17', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.71  thf(cc5_funct_2, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.71       ( ![C:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.71             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.71  thf('18', plain,
% 0.46/0.71      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.46/0.71          | (v1_partfun1 @ X38 @ X39)
% 0.46/0.71          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.46/0.71          | ~ (v1_funct_1 @ X38)
% 0.46/0.71          | (v1_xboole_0 @ X40))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.71  thf('19', plain,
% 0.46/0.71      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.46/0.71        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.71  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('21', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('22', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('23', plain,
% 0.46/0.71      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.71  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('25', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.71  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('27', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.71  thf('28', plain,
% 0.46/0.71      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.71        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['19', '20', '27'])).
% 0.46/0.71  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf(fc5_struct_0, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.71       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.46/0.71  thf('30', plain,
% 0.46/0.71      (![X47 : $i]:
% 0.46/0.71         (~ (v1_xboole_0 @ (k2_struct_0 @ X47))
% 0.46/0.71          | ~ (l1_struct_0 @ X47)
% 0.46/0.71          | (v2_struct_0 @ X47))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.46/0.71  thf('31', plain,
% 0.46/0.71      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.71        | (v2_struct_0 @ sk_B)
% 0.46/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.71  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('33', plain,
% 0.46/0.71      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.71  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('35', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('clc', [status(thm)], ['33', '34'])).
% 0.46/0.71  thf('36', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('clc', [status(thm)], ['28', '35'])).
% 0.46/0.71  thf(d4_partfun1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.71       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.71  thf('37', plain,
% 0.46/0.71      (![X41 : $i, X42 : $i]:
% 0.46/0.71         (~ (v1_partfun1 @ X42 @ X41)
% 0.46/0.71          | ((k1_relat_1 @ X42) = (X41))
% 0.46/0.71          | ~ (v4_relat_1 @ X42 @ X41)
% 0.46/0.71          | ~ (v1_relat_1 @ X42))),
% 0.46/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.71  thf('38', plain,
% 0.46/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.71        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.71  thf('39', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(cc2_relat_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( v1_relat_1 @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.71  thf('40', plain,
% 0.46/0.71      (![X6 : $i, X7 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.46/0.71          | (v1_relat_1 @ X6)
% 0.46/0.71          | ~ (v1_relat_1 @ X7))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.71  thf('41', plain,
% 0.46/0.71      ((~ (v1_relat_1 @ 
% 0.46/0.71           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.71        | (v1_relat_1 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.71  thf(fc6_relat_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.71  thf('42', plain,
% 0.46/0.71      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.71  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('44', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(cc2_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.71  thf('45', plain,
% 0.46/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.71         ((v4_relat_1 @ X21 @ X22)
% 0.46/0.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.71  thf('46', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.71  thf('47', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.46/0.71  thf('48', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.46/0.71  thf('49', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('50', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('51', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('52', plain,
% 0.46/0.71      (((m1_subset_1 @ sk_C @ 
% 0.46/0.71         (k1_zfmisc_1 @ 
% 0.46/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.71  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('54', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.71  thf('55', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('56', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('clc', [status(thm)], ['28', '35'])).
% 0.46/0.71  thf('57', plain,
% 0.46/0.71      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.71  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('59', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.71  thf('60', plain,
% 0.46/0.71      (![X41 : $i, X42 : $i]:
% 0.46/0.71         (~ (v1_partfun1 @ X42 @ X41)
% 0.46/0.71          | ((k1_relat_1 @ X42) = (X41))
% 0.46/0.71          | ~ (v4_relat_1 @ X42 @ X41)
% 0.46/0.71          | ~ (v1_relat_1 @ X42))),
% 0.46/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.71  thf('61', plain,
% 0.46/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.71        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.71  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('63', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.71  thf('64', plain,
% 0.46/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.71         ((v4_relat_1 @ X21 @ X22)
% 0.46/0.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.71  thf('65', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.71  thf('66', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.71  thf('67', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['54', '66'])).
% 0.46/0.71  thf(d4_tops_2, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.71       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.71         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.71  thf('68', plain,
% 0.46/0.71      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.46/0.71         (((k2_relset_1 @ X49 @ X48 @ X50) != (X48))
% 0.46/0.71          | ~ (v2_funct_1 @ X50)
% 0.46/0.71          | ((k2_tops_2 @ X49 @ X48 @ X50) = (k2_funct_1 @ X50))
% 0.46/0.71          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.46/0.71          | ~ (v1_funct_2 @ X50 @ X49 @ X48)
% 0.46/0.71          | ~ (v1_funct_1 @ X50))),
% 0.46/0.71      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.71  thf('69', plain,
% 0.46/0.71      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71            = (k2_funct_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.71        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71            != (u1_struct_0 @ sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.71  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('71', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('72', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('73', plain,
% 0.46/0.71      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup+', [status(thm)], ['71', '72'])).
% 0.46/0.71  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('75', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.71  thf('76', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.71  thf('77', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.71  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('79', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.71  thf('80', plain,
% 0.46/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.71         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.46/0.71          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.71  thf('81', plain,
% 0.46/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71         = (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['79', '80'])).
% 0.46/0.71  thf('82', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.71  thf('83', plain,
% 0.46/0.71      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71         = (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.71  thf('84', plain,
% 0.46/0.71      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71          = (k2_funct_1 @ sk_C))
% 0.46/0.71        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['69', '70', '77', '78', '83'])).
% 0.46/0.71  thf('85', plain,
% 0.46/0.71      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.71        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71            = (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['49', '84'])).
% 0.46/0.71  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('88', plain,
% 0.46/0.71      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.71        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71            = (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.46/0.71  thf('89', plain,
% 0.46/0.71      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71         = (k2_funct_1 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['88'])).
% 0.46/0.71  thf('90', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('91', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.71  thf('92', plain,
% 0.46/0.71      (((m1_subset_1 @ sk_C @ 
% 0.46/0.71         (k1_zfmisc_1 @ 
% 0.46/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['90', '91'])).
% 0.46/0.71  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('94', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['92', '93'])).
% 0.46/0.71  thf('95', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('96', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)], ['94', '95'])).
% 0.46/0.71  thf('97', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.71  thf('98', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)], ['96', '97'])).
% 0.46/0.71  thf(t31_funct_2, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.71       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.71         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.71           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.71           ( m1_subset_1 @
% 0.46/0.71             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.71  thf('99', plain,
% 0.46/0.71      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.46/0.71         (~ (v2_funct_1 @ X43)
% 0.46/0.71          | ((k2_relset_1 @ X45 @ X44 @ X43) != (X44))
% 0.46/0.71          | (m1_subset_1 @ (k2_funct_1 @ X43) @ 
% 0.46/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.46/0.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.46/0.71          | ~ (v1_funct_2 @ X43 @ X45 @ X44)
% 0.46/0.71          | ~ (v1_funct_1 @ X43))),
% 0.46/0.71      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.71  thf('100', plain,
% 0.46/0.71      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.71           (k1_zfmisc_1 @ 
% 0.46/0.71            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.46/0.71        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.71            != (k2_relat_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['98', '99'])).
% 0.46/0.71  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('102', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('103', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.71  thf('104', plain,
% 0.46/0.71      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['102', '103'])).
% 0.46/0.71  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('106', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['104', '105'])).
% 0.46/0.71  thf('107', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('108', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.71  thf('109', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.71  thf('110', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['108', '109'])).
% 0.46/0.71  thf('111', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('112', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('113', plain,
% 0.46/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71         = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('114', plain,
% 0.46/0.71      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71          = (k2_struct_0 @ sk_B))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup+', [status(thm)], ['112', '113'])).
% 0.46/0.71  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('116', plain,
% 0.46/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71         = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['114', '115'])).
% 0.46/0.71  thf('117', plain,
% 0.46/0.71      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71          = (k2_struct_0 @ sk_B))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['111', '116'])).
% 0.46/0.71  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('119', plain,
% 0.46/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71         = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['117', '118'])).
% 0.46/0.71  thf('120', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('121', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('122', plain,
% 0.46/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.71         = (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.46/0.71  thf('123', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.71  thf('124', plain,
% 0.46/0.71      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.71         = (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['122', '123'])).
% 0.46/0.71  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('126', plain,
% 0.46/0.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.71         (k1_zfmisc_1 @ 
% 0.46/0.71          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.46/0.71        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['100', '101', '110', '124', '125'])).
% 0.46/0.71  thf('127', plain,
% 0.46/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.71      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.71  thf('128', plain,
% 0.46/0.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.71         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.46/0.71          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.71  thf('129', plain,
% 0.46/0.71      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.71  thf(dt_k2_funct_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.71  thf('130', plain,
% 0.46/0.71      (![X13 : $i]:
% 0.46/0.71         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.46/0.71          | ~ (v1_funct_1 @ X13)
% 0.46/0.71          | ~ (v1_relat_1 @ X13))),
% 0.46/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.71  thf(t155_funct_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.71       ( ( v2_funct_1 @ B ) =>
% 0.46/0.71         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.46/0.71  thf('131', plain,
% 0.46/0.71      (![X15 : $i, X16 : $i]:
% 0.46/0.71         (~ (v2_funct_1 @ X15)
% 0.46/0.71          | ((k10_relat_1 @ X15 @ X16)
% 0.46/0.71              = (k9_relat_1 @ (k2_funct_1 @ X15) @ X16))
% 0.46/0.71          | ~ (v1_funct_1 @ X15)
% 0.46/0.71          | ~ (v1_relat_1 @ X15))),
% 0.46/0.71      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.46/0.71  thf(t146_relat_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( v1_relat_1 @ A ) =>
% 0.46/0.71       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.46/0.71  thf('132', plain,
% 0.46/0.71      (![X10 : $i]:
% 0.46/0.71         (((k9_relat_1 @ X10 @ (k1_relat_1 @ X10)) = (k2_relat_1 @ X10))
% 0.46/0.71          | ~ (v1_relat_1 @ X10))),
% 0.46/0.71      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.46/0.71  thf('133', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['131', '132'])).
% 0.46/0.71  thf('134', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['130', '133'])).
% 0.46/0.71  thf('135', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0))),
% 0.46/0.71      inference('simplify', [status(thm)], ['134'])).
% 0.46/0.71  thf('136', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(dt_k8_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.71  thf('137', plain,
% 0.46/0.71      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.46/0.71          | (m1_subset_1 @ (k8_relset_1 @ X25 @ X26 @ X24 @ X27) @ 
% 0.46/0.71             (k1_zfmisc_1 @ X25)))),
% 0.46/0.71      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.46/0.71  thf('138', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (m1_subset_1 @ 
% 0.46/0.71          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.71           X0) @ 
% 0.46/0.71          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['136', '137'])).
% 0.46/0.71  thf(t3_subset, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.71  thf('139', plain,
% 0.46/0.71      (![X3 : $i, X4 : $i]:
% 0.46/0.71         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.71  thf('140', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (r1_tarski @ 
% 0.46/0.71          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.71           X0) @ 
% 0.46/0.71          (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['138', '139'])).
% 0.46/0.71  thf('141', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k8_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.46/0.71  thf('142', plain,
% 0.46/0.71      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.46/0.71          | ((k8_relset_1 @ X35 @ X36 @ X34 @ X37) = (k10_relat_1 @ X34 @ X37)))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.46/0.71  thf('143', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.71           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['141', '142'])).
% 0.46/0.71  thf('144', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['140', '143'])).
% 0.46/0.71  thf('145', plain,
% 0.46/0.71      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (u1_struct_0 @ sk_A))
% 0.46/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.71      inference('sup+', [status(thm)], ['135', '144'])).
% 0.46/0.71  thf('146', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('148', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('149', plain,
% 0.46/0.71      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 0.46/0.71  thf('150', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.46/0.71  thf('151', plain,
% 0.46/0.71      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['149', '150'])).
% 0.46/0.71  thf('152', plain,
% 0.46/0.71      (![X13 : $i]:
% 0.46/0.71         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 0.46/0.71          | ~ (v1_funct_1 @ X13)
% 0.46/0.71          | ~ (v1_relat_1 @ X13))),
% 0.46/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.71  thf('153', plain,
% 0.46/0.71      (![X13 : $i]:
% 0.46/0.71         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.46/0.71          | ~ (v1_funct_1 @ X13)
% 0.46/0.71          | ~ (v1_relat_1 @ X13))),
% 0.46/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.71  thf(t61_funct_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.71       ( ( v2_funct_1 @ A ) =>
% 0.46/0.71         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.46/0.71             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.46/0.71           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.46/0.71             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.71  thf('154', plain,
% 0.46/0.71      (![X19 : $i]:
% 0.46/0.71         (~ (v2_funct_1 @ X19)
% 0.46/0.71          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 0.46/0.71              = (k6_relat_1 @ (k2_relat_1 @ X19)))
% 0.46/0.71          | ~ (v1_funct_1 @ X19)
% 0.46/0.71          | ~ (v1_relat_1 @ X19))),
% 0.46/0.71      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.71  thf(t51_funct_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.71           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 0.46/0.71               ( v2_funct_1 @ A ) ) =>
% 0.46/0.71             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.46/0.71  thf('155', plain,
% 0.46/0.71      (![X17 : $i, X18 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ X17)
% 0.46/0.71          | ~ (v1_funct_1 @ X17)
% 0.46/0.71          | (r1_tarski @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X17))
% 0.46/0.71          | ((k2_relat_1 @ (k5_relat_1 @ X17 @ X18)) != (k2_relat_1 @ X18))
% 0.46/0.71          | ~ (v2_funct_1 @ X18)
% 0.46/0.71          | ~ (v1_funct_1 @ X18)
% 0.46/0.71          | ~ (v1_relat_1 @ X18))),
% 0.46/0.71      inference('cnf', [status(esa)], [t51_funct_1])).
% 0.46/0.71  thf('156', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) != (k2_relat_1 @ X0))
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['154', '155'])).
% 0.46/0.71  thf(t71_relat_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.71       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.71  thf('157', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.46/0.71      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.71  thf('158', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.71      inference('demod', [status(thm)], ['156', '157'])).
% 0.46/0.71  thf('159', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0))),
% 0.46/0.71      inference('simplify', [status(thm)], ['158'])).
% 0.46/0.71  thf('160', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['153', '159'])).
% 0.46/0.71  thf('161', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0))),
% 0.46/0.71      inference('simplify', [status(thm)], ['160'])).
% 0.46/0.71  thf('162', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['152', '161'])).
% 0.46/0.71  thf('163', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0))),
% 0.46/0.71      inference('simplify', [status(thm)], ['162'])).
% 0.46/0.71  thf(d10_xboole_0, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.71  thf('164', plain,
% 0.46/0.71      (![X0 : $i, X2 : $i]:
% 0.46/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.71  thf('165', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.71          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['163', '164'])).
% 0.46/0.71  thf('166', plain,
% 0.46/0.71      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['151', '165'])).
% 0.46/0.71  thf('167', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('170', plain,
% 0.46/0.71      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 0.46/0.71  thf('171', plain,
% 0.46/0.71      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['129', '170'])).
% 0.46/0.71  thf('172', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.71  thf('173', plain,
% 0.46/0.71      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_A))))),
% 0.46/0.71      inference('demod', [status(thm)],
% 0.46/0.71                ['5', '10', '47', '48', '89', '171', '172'])).
% 0.46/0.71  thf('174', plain,
% 0.46/0.71      (($false)
% 0.46/0.71         <= (~
% 0.46/0.71             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_A))))),
% 0.46/0.71      inference('simplify', [status(thm)], ['173'])).
% 0.46/0.71  thf('175', plain,
% 0.46/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.71      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.71  thf('176', plain,
% 0.46/0.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.71         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.46/0.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.71  thf('177', plain,
% 0.46/0.71      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['175', '176'])).
% 0.46/0.71  thf(fc6_funct_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.46/0.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.71         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.71  thf('178', plain,
% 0.46/0.71      (![X14 : $i]:
% 0.46/0.71         ((v2_funct_1 @ (k2_funct_1 @ X14))
% 0.46/0.71          | ~ (v2_funct_1 @ X14)
% 0.46/0.71          | ~ (v1_funct_1 @ X14)
% 0.46/0.71          | ~ (v1_relat_1 @ X14))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.71  thf('179', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('180', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['54', '66'])).
% 0.46/0.71  thf('181', plain,
% 0.46/0.71      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.46/0.71         (~ (v2_funct_1 @ X43)
% 0.46/0.71          | ((k2_relset_1 @ X45 @ X44 @ X43) != (X44))
% 0.46/0.71          | (v1_funct_1 @ (k2_funct_1 @ X43))
% 0.46/0.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.46/0.71          | ~ (v1_funct_2 @ X43 @ X45 @ X44)
% 0.46/0.71          | ~ (v1_funct_1 @ X43))),
% 0.46/0.71      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.71  thf('182', plain,
% 0.46/0.71      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.71        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71            != (u1_struct_0 @ sk_B))
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['180', '181'])).
% 0.46/0.71  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('184', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.71  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('186', plain,
% 0.46/0.71      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.71        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71            != (u1_struct_0 @ sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 0.46/0.71  thf('187', plain,
% 0.46/0.71      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.71         = (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.71  thf('188', plain,
% 0.46/0.71      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.71        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['186', '187'])).
% 0.46/0.71  thf('189', plain,
% 0.46/0.71      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.71        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.71        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['179', '188'])).
% 0.46/0.71  thf('190', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('191', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('192', plain,
% 0.46/0.71      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.71        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['189', '190', '191'])).
% 0.46/0.71  thf('193', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['192'])).
% 0.46/0.71  thf('194', plain,
% 0.46/0.71      (![X13 : $i]:
% 0.46/0.71         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.46/0.71          | ~ (v1_funct_1 @ X13)
% 0.46/0.71          | ~ (v1_relat_1 @ X13))),
% 0.46/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.71  thf(t65_funct_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.71       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.71  thf('195', plain,
% 0.46/0.71      (![X20 : $i]:
% 0.46/0.71         (~ (v2_funct_1 @ X20)
% 0.46/0.71          | ((k2_funct_1 @ (k2_funct_1 @ X20)) = (X20))
% 0.46/0.71          | ~ (v1_funct_1 @ X20)
% 0.46/0.71          | ~ (v1_relat_1 @ X20))),
% 0.46/0.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.71  thf('196', plain,
% 0.46/0.71      (![X19 : $i]:
% 0.46/0.71         (~ (v2_funct_1 @ X19)
% 0.46/0.71          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 0.46/0.71              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 0.46/0.71          | ~ (v1_funct_1 @ X19)
% 0.46/0.71          | ~ (v1_relat_1 @ X19))),
% 0.46/0.71      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.71  thf('197', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.71            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['195', '196'])).
% 0.46/0.71  thf('198', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.71              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['194', '197'])).
% 0.46/0.71  thf('199', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.71            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.71          | ~ (v2_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_relat_1 @ X0))),
% 0.46/0.71      inference('simplify', [status(thm)], ['198'])).
% 0.46/0.71  thf('200', plain,
% 0.46/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.71        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.71            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['193', '199'])).
% 0.46/0.71  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('203', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('204', plain,
% 0.46/0.71      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.71        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.71            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.71      inference('demod', [status(thm)], ['200', '201', '202', '203'])).
% 0.46/0.71  thf('205', plain,
% 0.46/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.71        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.71            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['178', '204'])).
% 0.46/0.71  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('207', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('208', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('209', plain,
% 0.46/0.71      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.71         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)], ['205', '206', '207', '208'])).
% 0.46/0.71  thf('210', plain,
% 0.46/0.71      (![X19 : $i]:
% 0.46/0.71         (~ (v2_funct_1 @ X19)
% 0.46/0.71          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 0.46/0.71              = (k6_relat_1 @ (k2_relat_1 @ X19)))
% 0.46/0.71          | ~ (v1_funct_1 @ X19)
% 0.46/0.71          | ~ (v1_relat_1 @ X19))),
% 0.46/0.71      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.71  thf('211', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.46/0.71      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.71  thf('212', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.46/0.71            = (k2_relat_1 @ X0))
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v2_funct_1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['210', '211'])).
% 0.46/0.71  thf('213', plain,
% 0.46/0.71      ((((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.46/0.71          = (k2_relat_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.71      inference('sup+', [status(thm)], ['209', '212'])).
% 0.46/0.71  thf('214', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.46/0.71      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.71  thf('215', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('218', plain,
% 0.46/0.71      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['213', '214', '215', '216', '217'])).
% 0.46/0.71  thf('219', plain,
% 0.46/0.71      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['177', '218'])).
% 0.46/0.71  thf('220', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('221', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)], ['96', '97'])).
% 0.46/0.71  thf('222', plain,
% 0.46/0.71      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.46/0.71         (((k2_relset_1 @ X49 @ X48 @ X50) != (X48))
% 0.46/0.71          | ~ (v2_funct_1 @ X50)
% 0.46/0.71          | ((k2_tops_2 @ X49 @ X48 @ X50) = (k2_funct_1 @ X50))
% 0.46/0.71          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.46/0.71          | ~ (v1_funct_2 @ X50 @ X49 @ X48)
% 0.46/0.71          | ~ (v1_funct_1 @ X50))),
% 0.46/0.71      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.71  thf('223', plain,
% 0.46/0.71      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.71        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.71            = (k2_funct_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.71        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.71            != (k2_relat_1 @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['221', '222'])).
% 0.46/0.71  thf('224', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('225', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['108', '109'])).
% 0.46/0.71  thf('226', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('227', plain,
% 0.46/0.71      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.71         = (k2_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['122', '123'])).
% 0.46/0.71  thf('228', plain,
% 0.46/0.71      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.71          = (k2_funct_1 @ sk_C))
% 0.46/0.71        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['223', '224', '225', '226', '227'])).
% 0.46/0.71  thf('229', plain,
% 0.46/0.71      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.71         = (k2_funct_1 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['228'])).
% 0.46/0.71  thf('230', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('231', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         (((k2_struct_0 @ X46) = (u1_struct_0 @ X46)) | ~ (l1_struct_0 @ X46))),
% 0.46/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.71  thf('232', plain,
% 0.46/0.71      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71          != (k2_struct_0 @ sk_B)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('split', [status(esa)], ['1'])).
% 0.46/0.71  thf('233', plain,
% 0.46/0.71      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71           != (k2_struct_0 @ sk_B))
% 0.46/0.71         | ~ (l1_struct_0 @ sk_B)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['231', '232'])).
% 0.46/0.71  thf('234', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('235', plain,
% 0.46/0.71      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71          != (k2_struct_0 @ sk_B)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['233', '234'])).
% 0.46/0.71  thf('236', plain,
% 0.46/0.71      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.46/0.71          != (k2_struct_0 @ sk_B)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['230', '235'])).
% 0.46/0.71  thf('237', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('238', plain,
% 0.46/0.71      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.46/0.71          != (k2_relat_1 @ sk_C)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['236', '237'])).
% 0.46/0.71  thf('239', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.46/0.71  thf('240', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.46/0.71  thf('241', plain,
% 0.46/0.71      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.46/0.71          != (k2_relat_1 @ sk_C)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['238', '239', '240'])).
% 0.46/0.71  thf('242', plain,
% 0.46/0.71      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['229', '241'])).
% 0.46/0.71  thf('243', plain,
% 0.46/0.71      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71           (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.46/0.71         | ~ (l1_struct_0 @ sk_B)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['220', '242'])).
% 0.46/0.71  thf('244', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('245', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('246', plain,
% 0.46/0.71      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['243', '244', '245'])).
% 0.46/0.71  thf('247', plain,
% 0.46/0.71      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71                = (k2_struct_0 @ sk_B))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['219', '246'])).
% 0.46/0.71  thf('248', plain,
% 0.46/0.71      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71          = (k2_struct_0 @ sk_B)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['247'])).
% 0.46/0.71  thf('249', plain,
% 0.46/0.71      (~
% 0.46/0.71       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71          = (k2_struct_0 @ sk_A))) | 
% 0.46/0.71       ~
% 0.46/0.71       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71          = (k2_struct_0 @ sk_B)))),
% 0.46/0.71      inference('split', [status(esa)], ['1'])).
% 0.46/0.71  thf('250', plain,
% 0.46/0.71      (~
% 0.46/0.71       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.71          = (k2_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sat_resolution*', [status(thm)], ['248', '249'])).
% 0.46/0.71  thf('251', plain, ($false),
% 0.46/0.71      inference('simpl_trail', [status(thm)], ['174', '250'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.55/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
