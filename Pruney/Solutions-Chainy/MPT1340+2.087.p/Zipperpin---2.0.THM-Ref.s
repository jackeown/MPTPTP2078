%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k8g5E56VVE

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:22 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  273 (1282 expanded)
%              Number of leaves         :   41 ( 393 expanded)
%              Depth                    :   38
%              Number of atoms          : 2480 (28326 expanded)
%              Number of equality atoms :  108 ( 849 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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

thf('2',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
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

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X21 @ X19 )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','24','27'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','41'])).

thf('43',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

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

thf('49',plain,(
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

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('60',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','56','57','60'])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('65',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','67','68'])).

thf('70',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['42','70'])).

thf('72',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('76',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('77',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

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

thf('84',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('89',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['94','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','86','93','105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
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

thf('110',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('112',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('113',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('116',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('121',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X22 ) @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('130',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('131',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('132',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('133',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('134',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('135',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('136',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('137',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('138',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('140',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('141',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('142',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('143',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('144',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != X13 )
      | ( v1_partfun1 @ X14 @ X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('145',plain,(
    ! [X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v4_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
      | ( v1_partfun1 @ X14 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','145'])).

thf('147',plain,(
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
    inference('sup-',[status(thm)],['142','146'])).

thf('148',plain,(
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
    inference('sup-',[status(thm)],['141','147'])).

thf('149',plain,(
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
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
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
    inference('sup-',[status(thm)],['140','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['139','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('154',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('155',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['152','155','156','157','158'])).

thf('160',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['118'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['137','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['167','168','169','170'])).

thf('172',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['136','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['135','176'])).

thf('178',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['118'])).

thf('179',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['134','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['133','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['185','186','187','188'])).

thf('190',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('191',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('193',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('194',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['132','194'])).

thf('196',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('197',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','196','197','198','199','200'])).

thf('202',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['131','201'])).

thf('203',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','119','128','202'])).

thf('204',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['76','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('207',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','206','207','208'])).

thf('210',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['75','209'])).

thf('211',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','210'])).

thf('212',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('213',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
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

thf('215',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_funct_2 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['213','219'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['212','223'])).

thf('225',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    $false ),
    inference(demod,[status(thm)],['211','226','227','228','229'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k8g5E56VVE
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.60  % Solved by: fo/fo7.sh
% 0.35/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.60  % done 229 iterations in 0.141s
% 0.35/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.60  % SZS output start Refutation
% 0.35/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.60  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.35/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.35/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.60  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.35/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.35/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.35/0.60  thf(t65_funct_1, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.60       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.35/0.60  thf('0', plain,
% 0.35/0.60      (![X6 : $i]:
% 0.35/0.60         (~ (v2_funct_1 @ X6)
% 0.35/0.60          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.35/0.60          | ~ (v1_funct_1 @ X6)
% 0.35/0.60          | ~ (v1_relat_1 @ X6))),
% 0.35/0.60      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.35/0.60  thf(d3_struct_0, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.35/0.60  thf('1', plain,
% 0.35/0.60      (![X25 : $i]:
% 0.35/0.60         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.60  thf('2', plain,
% 0.35/0.60      (![X25 : $i]:
% 0.35/0.60         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.60  thf('3', plain,
% 0.35/0.60      (![X25 : $i]:
% 0.35/0.60         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.60  thf(t64_tops_2, conjecture,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( l1_struct_0 @ A ) =>
% 0.35/0.60       ( ![B:$i]:
% 0.35/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.35/0.60           ( ![C:$i]:
% 0.35/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.35/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.35/0.60                 ( m1_subset_1 @
% 0.35/0.60                   C @ 
% 0.35/0.60                   ( k1_zfmisc_1 @
% 0.35/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.35/0.60               ( ( ( ( k2_relset_1 @
% 0.35/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.35/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.35/0.60                   ( v2_funct_1 @ C ) ) =>
% 0.35/0.60                 ( r2_funct_2 @
% 0.35/0.60                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.35/0.60                   ( k2_tops_2 @
% 0.35/0.60                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.35/0.60                     ( k2_tops_2 @
% 0.35/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.35/0.60                   C ) ) ) ) ) ) ))).
% 0.35/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.60    (~( ![A:$i]:
% 0.35/0.60        ( ( l1_struct_0 @ A ) =>
% 0.35/0.60          ( ![B:$i]:
% 0.35/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.35/0.60              ( ![C:$i]:
% 0.35/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.35/0.60                    ( v1_funct_2 @
% 0.35/0.60                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.35/0.60                    ( m1_subset_1 @
% 0.35/0.60                      C @ 
% 0.35/0.60                      ( k1_zfmisc_1 @
% 0.35/0.60                        ( k2_zfmisc_1 @
% 0.35/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.35/0.60                  ( ( ( ( k2_relset_1 @
% 0.35/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.35/0.60                        ( k2_struct_0 @ B ) ) & 
% 0.35/0.60                      ( v2_funct_1 @ C ) ) =>
% 0.35/0.60                    ( r2_funct_2 @
% 0.35/0.60                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.35/0.60                      ( k2_tops_2 @
% 0.35/0.60                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.35/0.60                        ( k2_tops_2 @
% 0.35/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.35/0.60                      C ) ) ) ) ) ) ) )),
% 0.35/0.60    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.35/0.60  thf('4', plain,
% 0.35/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.35/0.60          sk_C)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('5', plain,
% 0.35/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.35/0.60           sk_C)
% 0.35/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.60  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('7', plain,
% 0.35/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.35/0.60          sk_C)),
% 0.35/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.60  thf('8', plain,
% 0.35/0.60      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.35/0.60           sk_C)
% 0.35/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['2', '7'])).
% 0.35/0.60  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('10', plain,
% 0.35/0.60      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.35/0.60          sk_C)),
% 0.35/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.60  thf('11', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_C @ 
% 0.35/0.60        (k1_zfmisc_1 @ 
% 0.35/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(t132_funct_2, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( ( v1_funct_1 @ C ) & 
% 0.35/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.60       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.60           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.35/0.60           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.35/0.60  thf('12', plain,
% 0.35/0.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.60         (((X19) = (k1_xboole_0))
% 0.35/0.60          | ~ (v1_funct_1 @ X20)
% 0.35/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.35/0.60          | (v1_partfun1 @ X20 @ X21)
% 0.35/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.35/0.60          | ~ (v1_funct_2 @ X20 @ X21 @ X19)
% 0.35/0.60          | ~ (v1_funct_1 @ X20))),
% 0.35/0.60      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.35/0.60  thf('13', plain,
% 0.35/0.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.60         (~ (v1_funct_2 @ X20 @ X21 @ X19)
% 0.35/0.60          | (v1_partfun1 @ X20 @ X21)
% 0.35/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.35/0.60          | ~ (v1_funct_1 @ X20)
% 0.35/0.60          | ((X19) = (k1_xboole_0)))),
% 0.35/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.35/0.60  thf('14', plain,
% 0.35/0.60      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.60        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.35/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.35/0.60  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('16', plain,
% 0.35/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf('17', plain,
% 0.35/0.60      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.60        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.35/0.60  thf(d4_partfun1, axiom,
% 0.35/0.60    (![A:$i,B:$i]:
% 0.35/0.60     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.35/0.60       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.35/0.60  thf('18', plain,
% 0.35/0.60      (![X13 : $i, X14 : $i]:
% 0.35/0.60         (~ (v1_partfun1 @ X14 @ X13)
% 0.35/0.60          | ((k1_relat_1 @ X14) = (X13))
% 0.35/0.60          | ~ (v4_relat_1 @ X14 @ X13)
% 0.35/0.60          | ~ (v1_relat_1 @ X14))),
% 0.35/0.60      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.35/0.60  thf('19', plain,
% 0.35/0.60      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.60        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.35/0.60        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.60  thf('20', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_C @ 
% 0.35/0.60        (k1_zfmisc_1 @ 
% 0.35/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(cc2_relat_1, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( v1_relat_1 @ A ) =>
% 0.35/0.60       ( ![B:$i]:
% 0.35/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.60  thf('21', plain,
% 0.35/0.60      (![X0 : $i, X1 : $i]:
% 0.35/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.35/0.60          | (v1_relat_1 @ X0)
% 0.35/0.60          | ~ (v1_relat_1 @ X1))),
% 0.35/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.60  thf('22', plain,
% 0.35/0.60      ((~ (v1_relat_1 @ 
% 0.35/0.60           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.35/0.60        | (v1_relat_1 @ sk_C))),
% 0.35/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.60  thf(fc6_relat_1, axiom,
% 0.35/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.60  thf('23', plain,
% 0.35/0.60      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.35/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.60  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.60  thf('25', plain,
% 0.35/0.60      ((m1_subset_1 @ sk_C @ 
% 0.35/0.60        (k1_zfmisc_1 @ 
% 0.35/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.60  thf(cc2_relset_1, axiom,
% 0.35/0.60    (![A:$i,B:$i,C:$i]:
% 0.35/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.60  thf('26', plain,
% 0.35/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.60         ((v4_relat_1 @ X7 @ X8)
% 0.35/0.60          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.35/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.60  thf('27', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.60  thf('28', plain,
% 0.35/0.60      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.35/0.60        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.35/0.60      inference('demod', [status(thm)], ['19', '24', '27'])).
% 0.35/0.60  thf(fc2_struct_0, axiom,
% 0.35/0.60    (![A:$i]:
% 0.35/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.60       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.61  thf('29', plain,
% 0.35/0.61      (![X26 : $i]:
% 0.35/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.35/0.61          | ~ (l1_struct_0 @ X26)
% 0.35/0.61          | (v2_struct_0 @ X26))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.61  thf('30', plain,
% 0.35/0.61      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.35/0.61        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.35/0.61        | (v2_struct_0 @ sk_B)
% 0.35/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.35/0.61  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.61  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('33', plain,
% 0.35/0.61      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.35/0.61  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('35', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.35/0.61      inference('clc', [status(thm)], ['33', '34'])).
% 0.35/0.61  thf('36', plain,
% 0.35/0.61      (![X25 : $i]:
% 0.35/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.61  thf('37', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.35/0.61      inference('clc', [status(thm)], ['33', '34'])).
% 0.35/0.61  thf('38', plain,
% 0.35/0.61      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.61      inference('sup+', [status(thm)], ['36', '37'])).
% 0.35/0.61  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('40', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.35/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.61  thf('41', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.35/0.61      inference('demod', [status(thm)], ['35', '40'])).
% 0.35/0.61  thf('42', plain,
% 0.35/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.35/0.61          sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['10', '41'])).
% 0.35/0.61  thf('43', plain,
% 0.35/0.61      (![X25 : $i]:
% 0.35/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.61  thf('44', plain,
% 0.35/0.61      (![X25 : $i]:
% 0.35/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.61  thf('45', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('46', plain,
% 0.35/0.61      (((m1_subset_1 @ sk_C @ 
% 0.35/0.61         (k1_zfmisc_1 @ 
% 0.35/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.35/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.61      inference('sup+', [status(thm)], ['44', '45'])).
% 0.35/0.61  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('48', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.61  thf(d4_tops_2, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.61       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.35/0.61         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.35/0.61  thf('49', plain,
% 0.35/0.61      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.35/0.61         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.35/0.61          | ~ (v2_funct_1 @ X29)
% 0.35/0.61          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.35/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.35/0.61          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.35/0.61          | ~ (v1_funct_1 @ X29))),
% 0.35/0.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.35/0.61  thf('50', plain,
% 0.35/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.35/0.61        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61            = (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61            != (u1_struct_0 @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.61  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('52', plain,
% 0.35/0.61      (![X25 : $i]:
% 0.35/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.61  thf('53', plain,
% 0.35/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('54', plain,
% 0.35/0.61      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.35/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.61      inference('sup+', [status(thm)], ['52', '53'])).
% 0.35/0.61  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('56', plain,
% 0.35/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['54', '55'])).
% 0.35/0.61  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('58', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.61  thf('59', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.61         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.35/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.35/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.61  thf('60', plain,
% 0.35/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61         = (k2_relat_1 @ sk_C))),
% 0.35/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.35/0.61  thf('61', plain,
% 0.35/0.61      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61          = (k2_funct_1 @ sk_C))
% 0.35/0.61        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.35/0.61      inference('demod', [status(thm)], ['50', '51', '56', '57', '60'])).
% 0.35/0.61  thf('62', plain,
% 0.35/0.61      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.35/0.61        | ~ (l1_struct_0 @ sk_B)
% 0.35/0.61        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61            = (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['43', '61'])).
% 0.35/0.61  thf('63', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('64', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.61         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.35/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.35/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.61  thf('65', plain,
% 0.35/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61         = (k2_relat_1 @ sk_C))),
% 0.35/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.35/0.61  thf('66', plain,
% 0.35/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61         = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('67', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['65', '66'])).
% 0.35/0.61  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('69', plain,
% 0.35/0.61      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.35/0.61        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61            = (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('demod', [status(thm)], ['62', '67', '68'])).
% 0.35/0.61  thf('70', plain,
% 0.35/0.61      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61         = (k2_funct_1 @ sk_C))),
% 0.35/0.61      inference('simplify', [status(thm)], ['69'])).
% 0.35/0.61  thf('71', plain,
% 0.35/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61           (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61          sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['42', '70'])).
% 0.35/0.61  thf('72', plain,
% 0.35/0.61      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.61           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61            (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61           sk_C)
% 0.35/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['1', '71'])).
% 0.35/0.61  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['65', '66'])).
% 0.35/0.61  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('75', plain,
% 0.35/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.61          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61           (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61          sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.35/0.61  thf(fc6_funct_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.35/0.61       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.35/0.61         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.35/0.61         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.35/0.61  thf('76', plain,
% 0.35/0.61      (![X4 : $i]:
% 0.35/0.61         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.35/0.61          | ~ (v2_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_relat_1 @ X4))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.35/0.61  thf('77', plain,
% 0.35/0.61      (![X25 : $i]:
% 0.35/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.61  thf('78', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.61  thf('79', plain,
% 0.35/0.61      (((m1_subset_1 @ sk_C @ 
% 0.35/0.61         (k1_zfmisc_1 @ 
% 0.35/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.35/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['77', '78'])).
% 0.35/0.61  thf('80', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('81', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.35/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.35/0.61  thf('82', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['65', '66'])).
% 0.35/0.61  thf('83', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.35/0.61      inference('demod', [status(thm)], ['81', '82'])).
% 0.35/0.61  thf(t31_funct_2, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.61       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.35/0.61         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.35/0.61           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.35/0.61           ( m1_subset_1 @
% 0.35/0.61             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.35/0.61  thf('84', plain,
% 0.35/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.61         (~ (v2_funct_1 @ X22)
% 0.35/0.61          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.35/0.61          | (m1_subset_1 @ (k2_funct_1 @ X22) @ 
% 0.35/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.35/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.35/0.61          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.35/0.61          | ~ (v1_funct_1 @ X22))),
% 0.35/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.35/0.61  thf('85', plain,
% 0.35/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.35/0.61        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.61           (k1_zfmisc_1 @ 
% 0.35/0.61            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.35/0.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.35/0.61            != (k2_relat_1 @ sk_C))
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.61      inference('sup-', [status(thm)], ['83', '84'])).
% 0.35/0.61  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('87', plain,
% 0.35/0.61      (![X25 : $i]:
% 0.35/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.61  thf('88', plain,
% 0.35/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['54', '55'])).
% 0.35/0.61  thf('89', plain,
% 0.35/0.61      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.35/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['87', '88'])).
% 0.35/0.61  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('91', plain,
% 0.35/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['89', '90'])).
% 0.35/0.61  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['65', '66'])).
% 0.35/0.61  thf('93', plain,
% 0.35/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.35/0.61      inference('demod', [status(thm)], ['91', '92'])).
% 0.35/0.61  thf('94', plain,
% 0.35/0.61      (![X25 : $i]:
% 0.35/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.61  thf('95', plain,
% 0.35/0.61      (![X25 : $i]:
% 0.35/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.61  thf('96', plain,
% 0.35/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61         = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('97', plain,
% 0.35/0.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61          = (k2_struct_0 @ sk_B))
% 0.35/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.61      inference('sup+', [status(thm)], ['95', '96'])).
% 0.35/0.61  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('99', plain,
% 0.35/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61         = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['97', '98'])).
% 0.35/0.61  thf('100', plain,
% 0.35/0.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61          = (k2_struct_0 @ sk_B))
% 0.35/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['94', '99'])).
% 0.35/0.61  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('102', plain,
% 0.35/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.35/0.61         = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['100', '101'])).
% 0.35/0.61  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['65', '66'])).
% 0.35/0.61  thf('104', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.35/0.61      inference('sup+', [status(thm)], ['65', '66'])).
% 0.35/0.61  thf('105', plain,
% 0.35/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.35/0.61         = (k2_relat_1 @ sk_C))),
% 0.35/0.61      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.35/0.61  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('107', plain,
% 0.35/0.61      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.61         (k1_zfmisc_1 @ 
% 0.35/0.61          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.35/0.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.35/0.61      inference('demod', [status(thm)], ['85', '86', '93', '105', '106'])).
% 0.35/0.61  thf('108', plain,
% 0.35/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.35/0.61      inference('simplify', [status(thm)], ['107'])).
% 0.35/0.61  thf('109', plain,
% 0.35/0.61      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.35/0.61         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.35/0.61          | ~ (v2_funct_1 @ X29)
% 0.35/0.61          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.35/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.35/0.61          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.35/0.61          | ~ (v1_funct_1 @ X29))),
% 0.35/0.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.35/0.61  thf('110', plain,
% 0.35/0.61      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.35/0.61             (k2_struct_0 @ sk_A))
% 0.35/0.61        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['108', '109'])).
% 0.35/0.61  thf('111', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.35/0.61      inference('demod', [status(thm)], ['81', '82'])).
% 0.35/0.61  thf('112', plain,
% 0.35/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.61         (~ (v2_funct_1 @ X22)
% 0.35/0.61          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.35/0.61          | (v1_funct_1 @ (k2_funct_1 @ X22))
% 0.35/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.35/0.61          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.35/0.61          | ~ (v1_funct_1 @ X22))),
% 0.35/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.35/0.61  thf('113', plain,
% 0.35/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.35/0.61        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.35/0.61            != (k2_relat_1 @ sk_C))
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.61      inference('sup-', [status(thm)], ['111', '112'])).
% 0.35/0.61  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('115', plain,
% 0.35/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.35/0.61      inference('demod', [status(thm)], ['91', '92'])).
% 0.35/0.61  thf('116', plain,
% 0.35/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.35/0.61         = (k2_relat_1 @ sk_C))),
% 0.35/0.61      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.35/0.61  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('118', plain,
% 0.35/0.61      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.35/0.61      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.35/0.61  thf('119', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.35/0.61      inference('simplify', [status(thm)], ['118'])).
% 0.35/0.61  thf('120', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.35/0.61      inference('demod', [status(thm)], ['81', '82'])).
% 0.35/0.61  thf('121', plain,
% 0.35/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.61         (~ (v2_funct_1 @ X22)
% 0.35/0.61          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.35/0.61          | (v1_funct_2 @ (k2_funct_1 @ X22) @ X23 @ X24)
% 0.35/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.35/0.61          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.35/0.61          | ~ (v1_funct_1 @ X22))),
% 0.35/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.35/0.61  thf('122', plain,
% 0.35/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.35/0.61        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.35/0.61           (k2_struct_0 @ sk_A))
% 0.35/0.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.35/0.61            != (k2_relat_1 @ sk_C))
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.61      inference('sup-', [status(thm)], ['120', '121'])).
% 0.35/0.61  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('124', plain,
% 0.35/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.35/0.61      inference('demod', [status(thm)], ['91', '92'])).
% 0.35/0.61  thf('125', plain,
% 0.35/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.35/0.61         = (k2_relat_1 @ sk_C))),
% 0.35/0.61      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.35/0.61  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('127', plain,
% 0.35/0.61      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.35/0.61         (k2_struct_0 @ sk_A))
% 0.35/0.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.35/0.61      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.35/0.61  thf('128', plain,
% 0.35/0.61      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.35/0.61        (k2_struct_0 @ sk_A))),
% 0.35/0.61      inference('simplify', [status(thm)], ['127'])).
% 0.35/0.61  thf('129', plain,
% 0.35/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.35/0.61      inference('simplify', [status(thm)], ['107'])).
% 0.35/0.61  thf('130', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.61         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.35/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.35/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.61  thf('131', plain,
% 0.35/0.61      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['129', '130'])).
% 0.35/0.61  thf(t55_funct_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.61       ( ( v2_funct_1 @ A ) =>
% 0.35/0.61         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.35/0.61           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.61  thf('132', plain,
% 0.35/0.61      (![X5 : $i]:
% 0.35/0.61         (~ (v2_funct_1 @ X5)
% 0.35/0.61          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.35/0.61          | ~ (v1_funct_1 @ X5)
% 0.35/0.61          | ~ (v1_relat_1 @ X5))),
% 0.35/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.61  thf('133', plain,
% 0.35/0.61      (![X4 : $i]:
% 0.35/0.61         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.35/0.61          | ~ (v2_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_relat_1 @ X4))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.35/0.61  thf('134', plain,
% 0.35/0.61      (![X4 : $i]:
% 0.35/0.61         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.35/0.61          | ~ (v2_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_relat_1 @ X4))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.35/0.61  thf('135', plain,
% 0.35/0.61      (![X5 : $i]:
% 0.35/0.61         (~ (v2_funct_1 @ X5)
% 0.35/0.61          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.35/0.61          | ~ (v1_funct_1 @ X5)
% 0.35/0.61          | ~ (v1_relat_1 @ X5))),
% 0.35/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.61  thf('136', plain,
% 0.35/0.61      (![X6 : $i]:
% 0.35/0.61         (~ (v2_funct_1 @ X6)
% 0.35/0.61          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.35/0.61          | ~ (v1_funct_1 @ X6)
% 0.35/0.61          | ~ (v1_relat_1 @ X6))),
% 0.35/0.61      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.35/0.61  thf('137', plain,
% 0.35/0.61      (![X4 : $i]:
% 0.35/0.61         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.35/0.61          | ~ (v2_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_relat_1 @ X4))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.35/0.61  thf('138', plain,
% 0.35/0.61      (![X4 : $i]:
% 0.35/0.61         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.35/0.61          | ~ (v2_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_relat_1 @ X4))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.35/0.61  thf('139', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.35/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.61  thf('140', plain,
% 0.35/0.61      (![X4 : $i]:
% 0.35/0.61         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.35/0.61          | ~ (v2_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_funct_1 @ X4)
% 0.35/0.61          | ~ (v1_relat_1 @ X4))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.35/0.61  thf('141', plain,
% 0.35/0.61      (![X5 : $i]:
% 0.35/0.61         (~ (v2_funct_1 @ X5)
% 0.35/0.61          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.35/0.61          | ~ (v1_funct_1 @ X5)
% 0.35/0.61          | ~ (v1_relat_1 @ X5))),
% 0.35/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.61  thf('142', plain,
% 0.35/0.61      (![X6 : $i]:
% 0.35/0.61         (~ (v2_funct_1 @ X6)
% 0.35/0.61          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.35/0.61          | ~ (v1_funct_1 @ X6)
% 0.35/0.61          | ~ (v1_relat_1 @ X6))),
% 0.35/0.61      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.35/0.61  thf('143', plain,
% 0.35/0.61      (![X5 : $i]:
% 0.35/0.61         (~ (v2_funct_1 @ X5)
% 0.35/0.61          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.35/0.61          | ~ (v1_funct_1 @ X5)
% 0.35/0.61          | ~ (v1_relat_1 @ X5))),
% 0.35/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.61  thf('144', plain,
% 0.35/0.61      (![X13 : $i, X14 : $i]:
% 0.35/0.61         (((k1_relat_1 @ X14) != (X13))
% 0.35/0.61          | (v1_partfun1 @ X14 @ X13)
% 0.35/0.61          | ~ (v4_relat_1 @ X14 @ X13)
% 0.35/0.61          | ~ (v1_relat_1 @ X14))),
% 0.35/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.35/0.61  thf('145', plain,
% 0.35/0.61      (![X14 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X14)
% 0.35/0.61          | ~ (v4_relat_1 @ X14 @ (k1_relat_1 @ X14))
% 0.35/0.61          | (v1_partfun1 @ X14 @ (k1_relat_1 @ X14)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['144'])).
% 0.35/0.61  thf('146', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v2_funct_1 @ X0)
% 0.35/0.61          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.35/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['143', '145'])).
% 0.35/0.61  thf('147', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v2_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.35/0.61          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.35/0.61             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.35/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['142', '146'])).
% 0.35/0.61  thf('148', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v2_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.35/0.61             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.35/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.35/0.61          | ~ (v2_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['141', '147'])).
% 0.35/0.61  thf('149', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.35/0.61          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.35/0.61             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.35/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v2_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['148'])).
% 0.35/0.61  thf('150', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v2_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.35/0.61             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['140', '149'])).
% 0.35/0.61  thf('151', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.35/0.61           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.35/0.61          | ~ (v2_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_relat_1 @ X0)
% 0.35/0.61          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.35/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['150'])).
% 0.35/0.61  thf('152', plain,
% 0.35/0.61      ((~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.35/0.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.61        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['139', '151'])).
% 0.35/0.61  thf('153', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.61  thf('154', plain,
% 0.35/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.61         ((v4_relat_1 @ X7 @ X8)
% 0.35/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.35/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.61  thf('155', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['153', '154'])).
% 0.35/0.61  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('159', plain,
% 0.35/0.61      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.35/0.61      inference('demod', [status(thm)], ['152', '155', '156', '157', '158'])).
% 0.35/0.61  thf('160', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.35/0.61      inference('simplify', [status(thm)], ['118'])).
% 0.35/0.61  thf('161', plain,
% 0.35/0.61      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.35/0.61      inference('demod', [status(thm)], ['159', '160'])).
% 0.35/0.61  thf('162', plain,
% 0.35/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.61        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['138', '161'])).
% 0.35/0.61  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('166', plain,
% 0.35/0.61      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 0.35/0.61  thf('167', plain,
% 0.35/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.61        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['137', '166'])).
% 0.35/0.61  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('171', plain,
% 0.35/0.61      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.35/0.61        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('demod', [status(thm)], ['167', '168', '169', '170'])).
% 0.35/0.61  thf('172', plain,
% 0.35/0.61      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.35/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.61      inference('sup+', [status(thm)], ['136', '171'])).
% 0.35/0.61  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('175', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('176', plain,
% 0.35/0.61      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 0.35/0.61  thf('177', plain,
% 0.35/0.61      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.35/0.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['135', '176'])).
% 0.35/0.61  thf('178', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.35/0.61      inference('simplify', [status(thm)], ['118'])).
% 0.35/0.61  thf('179', plain,
% 0.35/0.61      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.35/0.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('demod', [status(thm)], ['177', '178'])).
% 0.35/0.61  thf('180', plain,
% 0.35/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['134', '179'])).
% 0.35/0.61  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('184', plain,
% 0.35/0.61      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 0.35/0.61  thf('185', plain,
% 0.35/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.61        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['133', '184'])).
% 0.35/0.61  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('189', plain,
% 0.35/0.61      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('demod', [status(thm)], ['185', '186', '187', '188'])).
% 0.35/0.61  thf('190', plain,
% 0.35/0.61      (![X13 : $i, X14 : $i]:
% 0.35/0.61         (~ (v1_partfun1 @ X14 @ X13)
% 0.35/0.61          | ((k1_relat_1 @ X14) = (X13))
% 0.35/0.61          | ~ (v4_relat_1 @ X14 @ X13)
% 0.35/0.61          | ~ (v1_relat_1 @ X14))),
% 0.35/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.35/0.61  thf('191', plain,
% 0.35/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.35/0.61        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['189', '190'])).
% 0.35/0.61  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('193', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.35/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.61  thf('194', plain,
% 0.35/0.61      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.35/0.61        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('demod', [status(thm)], ['191', '192', '193'])).
% 0.35/0.61  thf('195', plain,
% 0.35/0.61      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.35/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.61        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['132', '194'])).
% 0.35/0.61  thf('196', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.35/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.61  thf('197', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['153', '154'])).
% 0.35/0.61  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('201', plain,
% 0.35/0.61      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('demod', [status(thm)],
% 0.35/0.61                ['195', '196', '197', '198', '199', '200'])).
% 0.35/0.61  thf('202', plain,
% 0.35/0.61      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.35/0.61      inference('demod', [status(thm)], ['131', '201'])).
% 0.35/0.61  thf('203', plain,
% 0.35/0.61      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.35/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['110', '119', '128', '202'])).
% 0.35/0.61  thf('204', plain,
% 0.35/0.61      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.61        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('simplify', [status(thm)], ['203'])).
% 0.35/0.61  thf('205', plain,
% 0.35/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.61        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['76', '204'])).
% 0.35/0.61  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('207', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('208', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('209', plain,
% 0.35/0.61      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.35/0.61         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.61      inference('demod', [status(thm)], ['205', '206', '207', '208'])).
% 0.35/0.61  thf('210', plain,
% 0.35/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.61          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['75', '209'])).
% 0.35/0.61  thf('211', plain,
% 0.35/0.61      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.61           sk_C)
% 0.35/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.61      inference('sup-', [status(thm)], ['0', '210'])).
% 0.35/0.61  thf('212', plain,
% 0.35/0.61      (![X25 : $i]:
% 0.35/0.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.61  thf('213', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('214', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_C @ 
% 0.35/0.61        (k1_zfmisc_1 @ 
% 0.35/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(reflexivity_r2_funct_2, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.61         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.61       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.35/0.61  thf('215', plain,
% 0.35/0.61      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.61         ((r2_funct_2 @ X15 @ X16 @ X17 @ X17)
% 0.35/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.35/0.61          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.35/0.61          | ~ (v1_funct_1 @ X17)
% 0.35/0.61          | ~ (v1_funct_1 @ X18)
% 0.35/0.61          | ~ (v1_funct_2 @ X18 @ X15 @ X16)
% 0.35/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.35/0.61      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.35/0.61  thf('216', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (m1_subset_1 @ X0 @ 
% 0.35/0.61             (k1_zfmisc_1 @ 
% 0.35/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.35/0.61          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.35/0.61          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.61             sk_C))),
% 0.35/0.61      inference('sup-', [status(thm)], ['214', '215'])).
% 0.35/0.61  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('218', plain,
% 0.35/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('219', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (m1_subset_1 @ X0 @ 
% 0.35/0.61             (k1_zfmisc_1 @ 
% 0.35/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.35/0.61          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.35/0.61          | ~ (v1_funct_1 @ X0)
% 0.35/0.61          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.35/0.61             sk_C))),
% 0.35/0.61      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.35/0.61  thf('220', plain,
% 0.35/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.35/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['213', '219'])).
% 0.35/0.61  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('222', plain,
% 0.35/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('223', plain,
% 0.35/0.61      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['220', '221', '222'])).
% 0.35/0.61  thf('224', plain,
% 0.35/0.61      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.35/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.61      inference('sup+', [status(thm)], ['212', '223'])).
% 0.35/0.61  thf('225', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('226', plain,
% 0.35/0.61      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['224', '225'])).
% 0.35/0.61  thf('227', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('229', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('230', plain, ($false),
% 0.35/0.61      inference('demod', [status(thm)], ['211', '226', '227', '228', '229'])).
% 0.35/0.61  
% 0.35/0.61  % SZS output end Refutation
% 0.35/0.61  
% 0.35/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
