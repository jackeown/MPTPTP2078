%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8bJw6EWEKa

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:20 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  297 (4458 expanded)
%              Number of leaves         :   39 (1298 expanded)
%              Depth                    :   43
%              Number of atoms          : 2582 (96468 expanded)
%              Number of equality atoms :  114 (2677 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('2',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','8','9'])).

thf('11',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    inference('sup+',[status(thm)],['6','7'])).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
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
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    inference('sup+',[status(thm)],['6','7'])).

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
    inference('sup+',[status(thm)],['6','7'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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

thf('49',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('50',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('58',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('65',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','67'])).

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

thf('69',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','66'])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('81',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('82',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','66'])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','78','79','84'])).

thf('86',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','47','48','49','90'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('92',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('93',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('95',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','66'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

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

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('107',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','66'])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    inference('sup+',[status(thm)],['6','7'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','66'])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104','113','127','128'])).

thf('130',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','67'])).

thf('135',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('136',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('139',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('142',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','141'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('144',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('148',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X22 ) @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('149',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('152',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('153',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','150','151','152','153'])).

thf('155',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','146','155'])).

thf('157',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('158',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('159',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('160',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('161',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('162',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('163',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('164',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('165',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('166',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('167',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','66'])).

thf('168',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('170',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('171',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('172',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('173',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != X16 )
      | ( v1_partfun1 @ X17 @ X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('174',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v4_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
      | ( v1_partfun1 @ X17 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['172','174'])).

thf('176',plain,(
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
    inference('sup-',[status(thm)],['171','175'])).

thf('177',plain,(
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
    inference('sup-',[status(thm)],['170','176'])).

thf('178',plain,(
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
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['169','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['168','180'])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('186',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['145'])).

thf('187',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['165','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['164','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['163','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('200',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('203',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['162','202'])).

thf('204',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['145'])).

thf('205',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('208',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('210',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','210'])).

thf('212',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['161','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('214',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['212','213','214','215'])).

thf('217',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('218',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('220',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['160','220'])).

thf('222',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('223',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('224',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['221','222','223','224','225'])).

thf('227',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','226'])).

thf('228',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','227'])).

thf('229',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['92','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['230','231','232','233'])).

thf('235',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['91','234'])).

thf('236',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('238',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','67'])).

thf('242',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('243',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_funct_2 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('249',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('250',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['247','248','249','250'])).

thf('252',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['241','251'])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('255',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,(
    $false ),
    inference(demod,[status(thm)],['240','255'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8bJw6EWEKa
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 288 iterations in 0.126s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.59  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.40/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.59  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.40/0.59  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.40/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.59  thf(t65_funct_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.59       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      (![X6 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X6)
% 0.40/0.59          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.40/0.59          | ~ (v1_funct_1 @ X6)
% 0.40/0.59          | ~ (v1_relat_1 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.59  thf(d3_struct_0, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf(t64_tops_2, conjecture,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_struct_0 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ( ( ( k2_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                   ( v2_funct_1 @ C ) ) =>
% 0.40/0.59                 ( r2_funct_2 @
% 0.40/0.59                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.59                   ( k2_tops_2 @
% 0.40/0.59                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.59                     ( k2_tops_2 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.40/0.59                   C ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i]:
% 0.40/0.59        ( ( l1_struct_0 @ A ) =>
% 0.40/0.59          ( ![B:$i]:
% 0.40/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.59              ( ![C:$i]:
% 0.40/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                    ( v1_funct_2 @
% 0.40/0.59                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                    ( m1_subset_1 @
% 0.40/0.59                      C @ 
% 0.40/0.59                      ( k1_zfmisc_1 @
% 0.40/0.59                        ( k2_zfmisc_1 @
% 0.40/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59                  ( ( ( ( k2_relset_1 @
% 0.40/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                        ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                      ( v2_funct_1 @ C ) ) =>
% 0.40/0.59                    ( r2_funct_2 @
% 0.40/0.59                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.59                      ( k2_tops_2 @
% 0.40/0.59                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.59                        ( k2_tops_2 @
% 0.40/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.40/0.59                      C ) ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59          sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59           sk_C)
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.59         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('8', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59          sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['3', '8', '9'])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (((m1_subset_1 @ sk_C @ 
% 0.40/0.59         (k1_zfmisc_1 @ 
% 0.40/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.40/0.59  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.59  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.40/0.59      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.59  thf(cc5_funct_2, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.59       ( ![C:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.40/0.59             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.40/0.59          | (v1_partfun1 @ X13 @ X14)
% 0.40/0.59          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.40/0.59          | ~ (v1_funct_1 @ X13)
% 0.40/0.59          | (v1_xboole_0 @ X15))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.40/0.59        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['21', '22'])).
% 0.40/0.59  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.59  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.40/0.59        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['19', '20', '27'])).
% 0.40/0.59  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf(fc5_struct_0, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.59       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X26 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ (k2_struct_0 @ X26))
% 0.40/0.59          | ~ (l1_struct_0 @ X26)
% 0.40/0.59          | (v2_struct_0 @ X26))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.40/0.59        | (v2_struct_0 @ sk_B)
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.59  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('35', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('clc', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('36', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('clc', [status(thm)], ['28', '35'])).
% 0.40/0.59  thf(d4_partfun1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.40/0.59       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (~ (v1_partfun1 @ X17 @ X16)
% 0.40/0.59          | ((k1_relat_1 @ X17) = (X16))
% 0.40/0.59          | ~ (v4_relat_1 @ X17 @ X16)
% 0.40/0.59          | ~ (v1_relat_1 @ X17))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc2_relat_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.59          | (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ 
% 0.40/0.59           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.40/0.59        | (v1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.59  thf(fc6_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.59  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc2_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((v4_relat_1 @ X7 @ X8)
% 0.40/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.59  thf('46', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.59  thf('47', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.40/0.59  thf('48', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.40/0.59  thf('49', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (((m1_subset_1 @ sk_C @ 
% 0.40/0.59         (k1_zfmisc_1 @ 
% 0.40/0.59          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.40/0.59  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('57', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('clc', [status(thm)], ['28', '35'])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup+', [status(thm)], ['56', '57'])).
% 0.40/0.59  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('60', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['58', '59'])).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (~ (v1_partfun1 @ X17 @ X16)
% 0.40/0.59          | ((k1_relat_1 @ X17) = (X16))
% 0.40/0.59          | ~ (v4_relat_1 @ X17 @ X16)
% 0.40/0.59          | ~ (v1_relat_1 @ X17))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.59  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((v4_relat_1 @ X7 @ X8)
% 0.40/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.59  thf('66', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.59  thf('67', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['62', '63', '66'])).
% 0.40/0.59  thf('68', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['55', '67'])).
% 0.40/0.59  thf(d4_tops_2, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.40/0.59         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.40/0.59         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.40/0.59          | ~ (v2_funct_1 @ X29)
% 0.40/0.59          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.40/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.40/0.59          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.40/0.59          | ~ (v1_funct_1 @ X29))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.59  thf('70', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            = (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            != (u1_struct_0 @ sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['68', '69'])).
% 0.40/0.59  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('72', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('73', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('74', plain,
% 0.40/0.59      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup+', [status(thm)], ['72', '73'])).
% 0.40/0.59  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.59  thf('77', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['62', '63', '66'])).
% 0.40/0.59  thf('78', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['76', '77'])).
% 0.40/0.59  thf('79', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('80', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('81', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.59         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.59  thf('82', plain,
% 0.40/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['80', '81'])).
% 0.40/0.59  thf('83', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['62', '63', '66'])).
% 0.40/0.59  thf('84', plain,
% 0.40/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['82', '83'])).
% 0.40/0.59  thf('85', plain,
% 0.40/0.59      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59          = (k2_funct_1 @ sk_C))
% 0.40/0.59        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['70', '71', '78', '79', '84'])).
% 0.40/0.59  thf('86', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B)
% 0.40/0.59        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            = (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['50', '85'])).
% 0.40/0.59  thf('87', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('89', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.40/0.59        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            = (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.40/0.59  thf('90', plain,
% 0.40/0.59      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_funct_1 @ sk_C))),
% 0.40/0.59      inference('simplify', [status(thm)], ['89'])).
% 0.40/0.59  thf('91', plain,
% 0.40/0.59      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59           (k2_funct_1 @ sk_C)) @ 
% 0.40/0.59          sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['10', '47', '48', '49', '90'])).
% 0.40/0.59  thf(fc6_funct_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.40/0.59       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.40/0.59         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.40/0.59         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.40/0.59  thf('92', plain,
% 0.40/0.59      (![X4 : $i]:
% 0.40/0.59         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.40/0.59          | ~ (v2_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_relat_1 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.40/0.59  thf('93', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('94', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('95', plain,
% 0.40/0.59      (((m1_subset_1 @ sk_C @ 
% 0.40/0.59         (k1_zfmisc_1 @ 
% 0.40/0.59          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['93', '94'])).
% 0.40/0.59  thf('96', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('97', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['95', '96'])).
% 0.40/0.59  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('99', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.40/0.59      inference('demod', [status(thm)], ['97', '98'])).
% 0.40/0.59  thf('100', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['62', '63', '66'])).
% 0.40/0.59  thf('101', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.40/0.59      inference('demod', [status(thm)], ['99', '100'])).
% 0.40/0.59  thf(t31_funct_2, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.40/0.59         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.40/0.59           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.40/0.59           ( m1_subset_1 @
% 0.40/0.59             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.40/0.59  thf('102', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X22)
% 0.40/0.59          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.40/0.59          | (m1_subset_1 @ (k2_funct_1 @ X22) @ 
% 0.40/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.40/0.59          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.40/0.59          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.40/0.59          | ~ (v1_funct_1 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.40/0.59  thf('103', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.40/0.59        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.59           (k1_zfmisc_1 @ 
% 0.40/0.59            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.40/0.59        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.40/0.59            != (k2_relat_1 @ sk_C))
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['101', '102'])).
% 0.40/0.59  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('105', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('106', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.59  thf('107', plain,
% 0.40/0.59      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['105', '106'])).
% 0.40/0.59  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('109', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['107', '108'])).
% 0.40/0.59  thf('110', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('111', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['109', '110'])).
% 0.40/0.59  thf('112', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['62', '63', '66'])).
% 0.40/0.59  thf('113', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['111', '112'])).
% 0.40/0.59  thf('114', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('115', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('116', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('117', plain,
% 0.40/0.59      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59          = (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup+', [status(thm)], ['115', '116'])).
% 0.40/0.59  thf('118', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('119', plain,
% 0.40/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['117', '118'])).
% 0.40/0.59  thf('120', plain,
% 0.40/0.59      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59          = (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['114', '119'])).
% 0.40/0.59  thf('121', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('122', plain,
% 0.40/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['120', '121'])).
% 0.40/0.59  thf('123', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('124', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('125', plain,
% 0.40/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.40/0.59         = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.40/0.59  thf('126', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['62', '63', '66'])).
% 0.40/0.59  thf('127', plain,
% 0.40/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.40/0.59         = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['125', '126'])).
% 0.40/0.59  thf('128', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('129', plain,
% 0.40/0.59      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.59         (k1_zfmisc_1 @ 
% 0.40/0.59          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.40/0.59        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['103', '104', '113', '127', '128'])).
% 0.40/0.59  thf('130', plain,
% 0.40/0.59      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['129'])).
% 0.40/0.59  thf('131', plain,
% 0.40/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.40/0.59         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.40/0.59          | ~ (v2_funct_1 @ X29)
% 0.40/0.59          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.40/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.40/0.59          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.40/0.59          | ~ (v1_funct_1 @ X29))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.59  thf('132', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.40/0.59             (k1_relat_1 @ sk_C))
% 0.40/0.59        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['130', '131'])).
% 0.40/0.59  thf('133', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.59  thf('134', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['55', '67'])).
% 0.40/0.59  thf('135', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X22)
% 0.40/0.59          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.40/0.59          | (v1_funct_1 @ (k2_funct_1 @ X22))
% 0.40/0.59          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.40/0.59          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.40/0.59          | ~ (v1_funct_1 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.40/0.59  thf('136', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            != (u1_struct_0 @ sk_B))
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['134', '135'])).
% 0.40/0.59  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('138', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['76', '77'])).
% 0.40/0.59  thf('139', plain,
% 0.40/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['82', '83'])).
% 0.40/0.59  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('141', plain,
% 0.40/0.59      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 0.40/0.59  thf('142', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B)
% 0.40/0.59        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['133', '141'])).
% 0.40/0.59  thf('143', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf('144', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('145', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.40/0.59        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.40/0.59  thf('146', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.59      inference('simplify', [status(thm)], ['145'])).
% 0.40/0.59  thf('147', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.40/0.59      inference('demod', [status(thm)], ['99', '100'])).
% 0.40/0.59  thf('148', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X22)
% 0.40/0.59          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.40/0.59          | (v1_funct_2 @ (k2_funct_1 @ X22) @ X23 @ X24)
% 0.40/0.59          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.40/0.59          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.40/0.59          | ~ (v1_funct_1 @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.40/0.59  thf('149', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.40/0.59        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.40/0.59           (k1_relat_1 @ sk_C))
% 0.40/0.59        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.40/0.59            != (k2_relat_1 @ sk_C))
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['147', '148'])).
% 0.40/0.59  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('151', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['111', '112'])).
% 0.40/0.59  thf('152', plain,
% 0.40/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.40/0.59         = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['125', '126'])).
% 0.40/0.59  thf('153', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('154', plain,
% 0.40/0.59      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.40/0.59         (k1_relat_1 @ sk_C))
% 0.40/0.59        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['149', '150', '151', '152', '153'])).
% 0.40/0.59  thf('155', plain,
% 0.40/0.59      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.40/0.59        (k1_relat_1 @ sk_C))),
% 0.40/0.59      inference('simplify', [status(thm)], ['154'])).
% 0.40/0.59  thf('156', plain,
% 0.40/0.59      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['132', '146', '155'])).
% 0.40/0.59  thf('157', plain,
% 0.40/0.59      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['129'])).
% 0.40/0.59  thf('158', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.59         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.59  thf('159', plain,
% 0.40/0.59      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['157', '158'])).
% 0.40/0.59  thf(t55_funct_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.59       ( ( v2_funct_1 @ A ) =>
% 0.40/0.59         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.40/0.59           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.40/0.59  thf('160', plain,
% 0.40/0.59      (![X5 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X5)
% 0.40/0.59          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.40/0.59          | ~ (v1_funct_1 @ X5)
% 0.40/0.59          | ~ (v1_relat_1 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.59  thf('161', plain,
% 0.40/0.59      (![X4 : $i]:
% 0.40/0.59         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.40/0.59          | ~ (v2_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_relat_1 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.40/0.59  thf('162', plain,
% 0.40/0.59      (![X5 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X5)
% 0.40/0.59          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.40/0.59          | ~ (v1_funct_1 @ X5)
% 0.40/0.59          | ~ (v1_relat_1 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.59  thf('163', plain,
% 0.40/0.59      (![X6 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X6)
% 0.40/0.59          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.40/0.59          | ~ (v1_funct_1 @ X6)
% 0.40/0.59          | ~ (v1_relat_1 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.59  thf('164', plain,
% 0.40/0.59      (![X4 : $i]:
% 0.40/0.59         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.40/0.59          | ~ (v2_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_relat_1 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.40/0.59  thf('165', plain,
% 0.40/0.59      (![X4 : $i]:
% 0.40/0.59         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.40/0.59          | ~ (v2_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_relat_1 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.40/0.59  thf('166', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.59  thf('167', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['62', '63', '66'])).
% 0.40/0.59  thf('168', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['166', '167'])).
% 0.40/0.59  thf('169', plain,
% 0.40/0.59      (![X4 : $i]:
% 0.40/0.59         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.40/0.59          | ~ (v2_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_funct_1 @ X4)
% 0.40/0.59          | ~ (v1_relat_1 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.40/0.59  thf('170', plain,
% 0.40/0.59      (![X5 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X5)
% 0.40/0.59          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.40/0.59          | ~ (v1_funct_1 @ X5)
% 0.40/0.59          | ~ (v1_relat_1 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.59  thf('171', plain,
% 0.40/0.59      (![X6 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X6)
% 0.40/0.59          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.40/0.59          | ~ (v1_funct_1 @ X6)
% 0.40/0.59          | ~ (v1_relat_1 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.59  thf('172', plain,
% 0.40/0.59      (![X5 : $i]:
% 0.40/0.59         (~ (v2_funct_1 @ X5)
% 0.40/0.59          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.40/0.59          | ~ (v1_funct_1 @ X5)
% 0.40/0.59          | ~ (v1_relat_1 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.59  thf('173', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (((k1_relat_1 @ X17) != (X16))
% 0.40/0.59          | (v1_partfun1 @ X17 @ X16)
% 0.40/0.59          | ~ (v4_relat_1 @ X17 @ X16)
% 0.40/0.59          | ~ (v1_relat_1 @ X17))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.59  thf('174', plain,
% 0.40/0.59      (![X17 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X17)
% 0.40/0.59          | ~ (v4_relat_1 @ X17 @ (k1_relat_1 @ X17))
% 0.40/0.59          | (v1_partfun1 @ X17 @ (k1_relat_1 @ X17)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['173'])).
% 0.40/0.59  thf('175', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['172', '174'])).
% 0.40/0.59  thf('176', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.40/0.59          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.40/0.59             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.40/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['171', '175'])).
% 0.40/0.59  thf('177', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.40/0.59             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['170', '176'])).
% 0.40/0.59  thf('178', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.40/0.59          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.40/0.59             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.40/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['177'])).
% 0.40/0.59  thf('179', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.40/0.59             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['169', '178'])).
% 0.40/0.59  thf('180', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.40/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.40/0.59          | ~ (v2_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.40/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['179'])).
% 0.40/0.59  thf('181', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.40/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['168', '180'])).
% 0.40/0.59  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('184', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('185', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.40/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.40/0.59      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 0.40/0.59  thf('186', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.59      inference('simplify', [status(thm)], ['145'])).
% 0.40/0.59  thf('187', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.40/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.40/0.59      inference('demod', [status(thm)], ['185', '186'])).
% 0.40/0.59  thf('188', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.40/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['165', '187'])).
% 0.40/0.59  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('192', plain,
% 0.40/0.59      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.40/0.59         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 0.40/0.59  thf('193', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.40/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['164', '192'])).
% 0.40/0.59  thf('194', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('196', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('197', plain,
% 0.40/0.59      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.40/0.59        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.59      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 0.40/0.59  thf('198', plain,
% 0.40/0.59      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.59      inference('sup+', [status(thm)], ['163', '197'])).
% 0.40/0.59  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('202', plain,
% 0.40/0.59      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.59      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 0.40/0.59  thf('203', plain,
% 0.40/0.59      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.59        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['162', '202'])).
% 0.40/0.59  thf('204', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.59      inference('simplify', [status(thm)], ['145'])).
% 0.40/0.59  thf('205', plain,
% 0.40/0.59      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.59        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['203', '204'])).
% 0.40/0.59  thf('206', plain,
% 0.40/0.59      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['129'])).
% 0.40/0.59  thf('207', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.59          | (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_relat_1 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.59  thf('208', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ 
% 0.40/0.59           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.40/0.59        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['206', '207'])).
% 0.40/0.59  thf('209', plain,
% 0.40/0.59      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.59  thf('210', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['208', '209'])).
% 0.40/0.59  thf('211', plain,
% 0.40/0.59      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['205', '210'])).
% 0.40/0.59  thf('212', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['161', '211'])).
% 0.40/0.59  thf('213', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('214', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('215', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('216', plain,
% 0.40/0.59      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['212', '213', '214', '215'])).
% 0.40/0.59  thf('217', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (~ (v1_partfun1 @ X17 @ X16)
% 0.40/0.59          | ((k1_relat_1 @ X17) = (X16))
% 0.40/0.59          | ~ (v4_relat_1 @ X17 @ X16)
% 0.40/0.59          | ~ (v1_relat_1 @ X17))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.59  thf('218', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['216', '217'])).
% 0.40/0.59  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('220', plain,
% 0.40/0.59      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.59      inference('demod', [status(thm)], ['218', '219'])).
% 0.40/0.59  thf('221', plain,
% 0.40/0.59      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['160', '220'])).
% 0.40/0.59  thf('222', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['166', '167'])).
% 0.40/0.59  thf('223', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('224', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('225', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('226', plain,
% 0.40/0.59      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['221', '222', '223', '224', '225'])).
% 0.40/0.59  thf('227', plain,
% 0.40/0.59      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['159', '226'])).
% 0.40/0.59  thf('228', plain,
% 0.40/0.59      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['156', '227'])).
% 0.40/0.59  thf('229', plain,
% 0.40/0.59      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.59        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['228'])).
% 0.40/0.59  thf('230', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['92', '229'])).
% 0.40/0.59  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('234', plain,
% 0.40/0.59      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['230', '231', '232', '233'])).
% 0.40/0.59  thf('235', plain,
% 0.40/0.59      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['91', '234'])).
% 0.40/0.59  thf('236', plain,
% 0.40/0.59      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.59           sk_C)
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '235'])).
% 0.40/0.59  thf('237', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('238', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('239', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('240', plain,
% 0.40/0.59      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 0.40/0.59  thf('241', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['55', '67'])).
% 0.40/0.59  thf('242', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(reflexivity_r2_funct_2, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.59         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.40/0.59  thf('243', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.59         ((r2_funct_2 @ X18 @ X19 @ X20 @ X20)
% 0.40/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.40/0.59          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.40/0.59          | ~ (v1_funct_1 @ X20)
% 0.40/0.59          | ~ (v1_funct_1 @ X21)
% 0.40/0.59          | ~ (v1_funct_2 @ X21 @ X18 @ X19)
% 0.40/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.40/0.59      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.40/0.59  thf('244', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.40/0.59             (k1_zfmisc_1 @ 
% 0.40/0.59              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.40/0.59          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.59             sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['242', '243'])).
% 0.40/0.59  thf('245', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('246', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('247', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.40/0.59             (k1_zfmisc_1 @ 
% 0.40/0.59              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.40/0.59          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.59             sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['244', '245', '246'])).
% 0.40/0.59  thf('248', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.40/0.59  thf('249', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.40/0.59  thf('250', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['38', '43', '46'])).
% 0.40/0.59  thf('251', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X0 @ 
% 0.40/0.59             (k1_zfmisc_1 @ 
% 0.40/0.59              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.40/0.59          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.59             sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['247', '248', '249', '250'])).
% 0.40/0.59  thf('252', plain,
% 0.40/0.59      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['241', '251'])).
% 0.40/0.59  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('254', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['76', '77'])).
% 0.40/0.59  thf('255', plain,
% 0.40/0.59      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['252', '253', '254'])).
% 0.40/0.59  thf('256', plain, ($false), inference('demod', [status(thm)], ['240', '255'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.44/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
