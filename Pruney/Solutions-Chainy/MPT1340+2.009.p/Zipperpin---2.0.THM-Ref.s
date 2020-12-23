%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I2bdw6J5EB

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:06 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  288 (1690 expanded)
%              Number of leaves         :   38 ( 503 expanded)
%              Depth                    :   42
%              Number of atoms          : 2603 (37368 expanded)
%              Number of equality atoms :  113 (1098 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('38',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','41'])).

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
    inference(clc,[status(thm)],['36','46'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('57',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','46'])).

thf('59',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('65',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('71',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','71'])).

thf('73',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','72'])).

thf('74',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','72'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('76',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

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

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('109',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','85','96','97','109'])).

thf('111',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

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

thf('114',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('118',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('123',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('125',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('126',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('129',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['126','127','128','129','130'])).

thf('132',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('134',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('135',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('138',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','139'])).

thf('141',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('143',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('144',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('147',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('148',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('152',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','71'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('154',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('155',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('159',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('160',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['157','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['156','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != X15 )
      | ( v1_partfun1 @ X16 @ X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('169',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v4_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
      | ( v1_partfun1 @ X16 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['167','169'])).

thf('171',plain,(
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
    inference('sup-',[status(thm)],['155','170'])).

thf('172',plain,(
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
    inference('sup-',[status(thm)],['154','171'])).

thf('173',plain,(
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
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
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
    inference('sup-',[status(thm)],['153','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['152','175'])).

thf('177',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['150','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['149','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['148','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('203',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('205',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','71'])).

thf('206',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['147','206'])).

thf('208',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','71'])).

thf('209',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['207','208','209','210','211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('215',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['131'])).

thf('217',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['146','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('223',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['145','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['223','224','225','226'])).

thf('228',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['144','227'])).

thf('229',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','132','141','228'])).

thf('230',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['112','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('233',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['13','18','73','74','75','111','235'])).

thf('237',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','236'])).

thf('238',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('239',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_funct_2 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('240',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_funct_2 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['238','240'])).

thf('242',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    $false ),
    inference(demod,[status(thm)],['237','244','245','246','247'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I2bdw6J5EB
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 258 iterations in 0.167s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.64  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.64  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(t65_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      (![X2 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X2)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | ~ (v1_relat_1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf(d3_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf(t64_tops_2, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.64                 ( m1_subset_1 @
% 0.45/0.64                   C @ 
% 0.45/0.64                   ( k1_zfmisc_1 @
% 0.45/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.64               ( ( ( ( k2_relset_1 @
% 0.45/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.64                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.64                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.64                 ( r2_funct_2 @
% 0.45/0.64                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.64                   ( k2_tops_2 @
% 0.45/0.64                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.64                     ( k2_tops_2 @
% 0.45/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.64                   C ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( l1_struct_0 @ A ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.64              ( ![C:$i]:
% 0.45/0.64                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.64                    ( v1_funct_2 @
% 0.45/0.64                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.64                    ( m1_subset_1 @
% 0.45/0.64                      C @ 
% 0.45/0.64                      ( k1_zfmisc_1 @
% 0.45/0.64                        ( k2_zfmisc_1 @
% 0.45/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.64                  ( ( ( ( k2_relset_1 @
% 0.45/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.64                        ( k2_struct_0 @ B ) ) & 
% 0.45/0.64                      ( v2_funct_1 @ C ) ) =>
% 0.45/0.64                    ( r2_funct_2 @
% 0.45/0.64                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.64                      ( k2_tops_2 @
% 0.45/0.64                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.64                        ( k2_tops_2 @
% 0.45/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.64                      C ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '7'])).
% 0.45/0.64  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '10'])).
% 0.45/0.64  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('18', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('24', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.64  thf(cc5_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.64       ( ![C:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.64             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.45/0.64          | (v1_partfun1 @ X12 @ X13)
% 0.45/0.64          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.45/0.64          | ~ (v1_funct_1 @ X12)
% 0.45/0.64          | (v1_xboole_0 @ X14))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.64  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['27', '28', '35'])).
% 0.45/0.64  thf('37', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf(fc2_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.64       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.45/0.64          | ~ (l1_struct_0 @ X25)
% 0.45/0.64          | (v2_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.64          | ~ (l1_struct_0 @ X0)
% 0.45/0.64          | (v2_struct_0 @ X0)
% 0.45/0.64          | ~ (l1_struct_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_struct_0 @ X0)
% 0.45/0.64          | ~ (l1_struct_0 @ X0)
% 0.45/0.64          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['40'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.64        | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['37', '41'])).
% 0.45/0.64  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.64  thf('45', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('46', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('clc', [status(thm)], ['44', '45'])).
% 0.45/0.64  thf('47', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['36', '46'])).
% 0.45/0.64  thf(d4_partfun1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.64       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.64          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.64          | ~ (v1_relat_1 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( v1_relat_1 @ C ) ))).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X3)
% 0.45/0.64          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X6 @ X7)
% 0.45/0.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('55', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('56', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('58', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['36', '46'])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['57', '58'])).
% 0.45/0.64  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('61', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.64  thf('62', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.64          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.64          | ~ (v1_relat_1 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('63', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.64  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('65', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.64  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('69', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X6 @ X7)
% 0.45/0.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('71', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.64  thf('72', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['63', '64', '71'])).
% 0.45/0.64  thf('73', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['56', '72'])).
% 0.45/0.64  thf('74', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['56', '72'])).
% 0.45/0.64  thf('75', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('76', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('77', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf('78', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['76', '77'])).
% 0.45/0.64  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('80', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.64  thf('81', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('82', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.64  thf(d4_tops_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.64         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.64  thf('83', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.64          | ~ (v2_funct_1 @ X28)
% 0.45/0.64          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.64          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.64          | ~ (v1_funct_1 @ X28))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.64  thf('84', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['82', '83'])).
% 0.45/0.64  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('86', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('87', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('88', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('89', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['87', '88'])).
% 0.45/0.64  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('91', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.64  thf('92', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['86', '91'])).
% 0.45/0.64  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('94', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.64  thf('95', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('96', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['94', '95'])).
% 0.45/0.64  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('98', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('99', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('100', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('101', plain,
% 0.45/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['99', '100'])).
% 0.45/0.64  thf('102', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('103', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['101', '102'])).
% 0.45/0.64  thf('104', plain,
% 0.45/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['98', '103'])).
% 0.45/0.64  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('106', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['104', '105'])).
% 0.45/0.64  thf('107', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('108', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('109', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.45/0.64  thf('110', plain,
% 0.45/0.64      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64          = (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['84', '85', '96', '97', '109'])).
% 0.45/0.64  thf('111', plain,
% 0.45/0.64      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['110'])).
% 0.45/0.64  thf(fc6_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.64         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.64         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.64  thf('112', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('113', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.64  thf(t31_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.64         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.64           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.64           ( m1_subset_1 @
% 0.45/0.64             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('114', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X21)
% 0.45/0.64          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.64          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.64          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.64          | ~ (v1_funct_1 @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('115', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64           (k1_zfmisc_1 @ 
% 0.45/0.64            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['113', '114'])).
% 0.45/0.64  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('117', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['94', '95'])).
% 0.45/0.64  thf('118', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.45/0.64  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('120', plain,
% 0.45/0.64      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.45/0.64  thf('121', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['120'])).
% 0.45/0.64  thf('122', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.64          | ~ (v2_funct_1 @ X28)
% 0.45/0.64          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.64          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.64          | ~ (v1_funct_1 @ X28))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.64  thf('123', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64             (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['121', '122'])).
% 0.45/0.64  thf('124', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.64  thf('125', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X21)
% 0.45/0.64          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.64          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.45/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.64          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.64          | ~ (v1_funct_1 @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('126', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['124', '125'])).
% 0.45/0.64  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('128', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['94', '95'])).
% 0.45/0.64  thf('129', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.45/0.64  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('131', plain,
% 0.45/0.64      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['126', '127', '128', '129', '130'])).
% 0.45/0.64  thf('132', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['131'])).
% 0.45/0.64  thf('133', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.64  thf('134', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X21)
% 0.45/0.64          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.64          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.45/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.64          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.64          | ~ (v1_funct_1 @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('135', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64           (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['133', '134'])).
% 0.45/0.64  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('137', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['94', '95'])).
% 0.45/0.64  thf('138', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.45/0.64  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('140', plain,
% 0.45/0.64      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64         (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['135', '136', '137', '138', '139'])).
% 0.45/0.64  thf('141', plain,
% 0.45/0.64      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64        (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('simplify', [status(thm)], ['140'])).
% 0.45/0.64  thf('142', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['120'])).
% 0.45/0.64  thf('143', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('144', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['142', '143'])).
% 0.45/0.64  thf('145', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('146', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('147', plain,
% 0.45/0.64      (![X2 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X2)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | ~ (v1_relat_1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf('148', plain,
% 0.45/0.64      (![X2 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X2)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | ~ (v1_relat_1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf('149', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('150', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('151', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('152', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['63', '64', '71'])).
% 0.45/0.64  thf('153', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf(t55_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v2_funct_1 @ A ) =>
% 0.45/0.64         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.64           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('154', plain,
% 0.45/0.64      (![X1 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X1)
% 0.45/0.64          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.45/0.64          | ~ (v1_funct_1 @ X1)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('155', plain,
% 0.45/0.64      (![X2 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X2)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | ~ (v1_relat_1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf('156', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('157', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('158', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('159', plain,
% 0.45/0.64      (![X2 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X2)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | ~ (v1_relat_1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf('160', plain,
% 0.45/0.64      (![X1 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X1)
% 0.45/0.64          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.45/0.64          | ~ (v1_funct_1 @ X1)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('161', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['159', '160'])).
% 0.45/0.64  thf('162', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['158', '161'])).
% 0.45/0.64  thf('163', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['162'])).
% 0.45/0.64  thf('164', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['157', '163'])).
% 0.45/0.64  thf('165', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['164'])).
% 0.45/0.64  thf('166', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['156', '165'])).
% 0.45/0.64  thf('167', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['166'])).
% 0.45/0.64  thf('168', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         (((k1_relat_1 @ X16) != (X15))
% 0.45/0.64          | (v1_partfun1 @ X16 @ X15)
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.64          | ~ (v1_relat_1 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('169', plain,
% 0.45/0.64      (![X16 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X16)
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ (k1_relat_1 @ X16))
% 0.45/0.64          | (v1_partfun1 @ X16 @ (k1_relat_1 @ X16)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['168'])).
% 0.45/0.64  thf('170', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['167', '169'])).
% 0.45/0.64  thf('171', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['155', '170'])).
% 0.45/0.64  thf('172', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['154', '171'])).
% 0.45/0.64  thf('173', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['172'])).
% 0.45/0.64  thf('174', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['153', '173'])).
% 0.45/0.64  thf('175', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['174'])).
% 0.45/0.64  thf('176', plain,
% 0.45/0.64      ((~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['152', '175'])).
% 0.45/0.64  thf('177', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.64  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('181', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['176', '177', '178', '179', '180'])).
% 0.45/0.64  thf('182', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['151', '181'])).
% 0.45/0.64  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('186', plain,
% 0.45/0.64      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 0.45/0.64  thf('187', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['150', '186'])).
% 0.45/0.64  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('191', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 0.45/0.64  thf('192', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['149', '191'])).
% 0.45/0.64  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('195', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('196', plain,
% 0.45/0.64      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 0.45/0.64  thf('197', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup+', [status(thm)], ['148', '196'])).
% 0.45/0.64  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('201', plain,
% 0.45/0.64      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 0.45/0.64  thf('202', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.64          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.64          | ~ (v1_relat_1 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('203', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ 
% 0.45/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ((k1_relat_1 @ sk_C)
% 0.45/0.64            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['201', '202'])).
% 0.45/0.64  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('205', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['63', '64', '71'])).
% 0.45/0.64  thf('206', plain,
% 0.45/0.64      ((~ (v4_relat_1 @ sk_C @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ((k2_struct_0 @ sk_A)
% 0.45/0.64            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['203', '204', '205'])).
% 0.45/0.64  thf('207', plain,
% 0.45/0.64      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k2_struct_0 @ sk_A)
% 0.45/0.64            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['147', '206'])).
% 0.45/0.64  thf('208', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['63', '64', '71'])).
% 0.45/0.64  thf('209', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.64  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('213', plain,
% 0.45/0.64      (((k2_struct_0 @ sk_A)
% 0.45/0.64         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)],
% 0.45/0.64                ['207', '208', '209', '210', '211', '212'])).
% 0.45/0.64  thf('214', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['166'])).
% 0.45/0.64  thf('215', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['213', '214'])).
% 0.45/0.64  thf('216', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['131'])).
% 0.45/0.64  thf('217', plain,
% 0.45/0.64      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['215', '216'])).
% 0.45/0.64  thf('218', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['146', '217'])).
% 0.45/0.64  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('221', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('222', plain,
% 0.45/0.64      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 0.45/0.64  thf('223', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['145', '222'])).
% 0.45/0.64  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('226', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('227', plain,
% 0.45/0.64      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['223', '224', '225', '226'])).
% 0.45/0.64  thf('228', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['144', '227'])).
% 0.45/0.64  thf('229', plain,
% 0.45/0.64      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['123', '132', '141', '228'])).
% 0.45/0.64  thf('230', plain,
% 0.45/0.64      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['229'])).
% 0.45/0.64  thf('231', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['112', '230'])).
% 0.45/0.64  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('233', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('234', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('235', plain,
% 0.45/0.64      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 0.45/0.64  thf('236', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)],
% 0.45/0.64                ['13', '18', '73', '74', '75', '111', '235'])).
% 0.45/0.64  thf('237', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['0', '236'])).
% 0.45/0.64  thf('238', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf(redefinition_r2_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.64         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.45/0.64  thf('239', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.64          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.45/0.64          | ~ (v1_funct_1 @ X17)
% 0.45/0.64          | ~ (v1_funct_1 @ X20)
% 0.45/0.64          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.45/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.64          | (r2_funct_2 @ X18 @ X19 @ X17 @ X20)
% 0.45/0.64          | ((X17) != (X20)))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.45/0.64  thf('240', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         ((r2_funct_2 @ X18 @ X19 @ X20 @ X20)
% 0.45/0.64          | ~ (v1_funct_1 @ X20)
% 0.45/0.64          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.45/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['239'])).
% 0.45/0.64  thf('241', plain,
% 0.45/0.64      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64           sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['238', '240'])).
% 0.45/0.64  thf('242', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.64  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('244', plain,
% 0.45/0.64      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['241', '242', '243'])).
% 0.45/0.64  thf('245', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('247', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('248', plain, ($false),
% 0.45/0.64      inference('demod', [status(thm)], ['237', '244', '245', '246', '247'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
