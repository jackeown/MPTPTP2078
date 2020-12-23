%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vx56R1d0px

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:06 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  292 (1907 expanded)
%              Number of leaves         :   38 ( 564 expanded)
%              Depth                    :   43
%              Number of atoms          : 2647 (42107 expanded)
%              Number of equality atoms :  111 (1225 expanded)
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

thf('3',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('17',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','19'])).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('52',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','41'])).

thf('54',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('60',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','66'])).

thf('68',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('70',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','67'])).

thf('71',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','67'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('73',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','68','69','70','71','72'])).

thf('74',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

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

thf('81',plain,(
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

thf('82',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    inference('sup+',[status(thm)],['17','18'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83','94','95','107'])).

thf('109',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['73','109'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
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

thf('122',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('124',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('128',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('133',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('142',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('149',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('150',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
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
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
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
    inference('sup-',[status(thm)],['147','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['146','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('159',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('163',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','66'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('165',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('166',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

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
    inference('sup-',[status(thm)],['166','170'])).

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
    inference('sup-',[status(thm)],['165','171'])).

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
    inference('sup-',[status(thm)],['164','173'])).

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
    inference('sup-',[status(thm)],['163','175'])).

thf('177',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

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
    inference('sup-',[status(thm)],['162','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

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
    inference('sup-',[status(thm)],['161','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

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
    inference('sup-',[status(thm)],['160','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

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
    inference('sup+',[status(thm)],['159','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

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
    inference('sup-',[status(thm)],['45','46'])).

thf('205',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','66'])).

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
    inference('sup-',[status(thm)],['158','206'])).

thf('208',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','66'])).

thf('209',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

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

thf('214',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['157','213'])).

thf('215',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('216',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['145','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('222',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['144','221'])).

thf('223',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('224',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['222','223','224','225'])).

thf('227',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['143','226'])).

thf('228',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','131','140','227'])).

thf('229',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['111','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['230','231','232','233'])).

thf('235',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['110','234'])).

thf('236',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('238',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('242',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_funct_2 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['241','247'])).

thf('249',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('251',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['248','249','250'])).

thf('252',plain,(
    $false ),
    inference(demod,[status(thm)],['240','251'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vx56R1d0px
% 0.16/0.37  % Computer   : n010.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:50:30 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.50/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.70  % Solved by: fo/fo7.sh
% 0.50/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.70  % done 422 iterations in 0.213s
% 0.50/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.70  % SZS output start Refutation
% 0.50/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.50/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.50/0.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.50/0.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.50/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.70  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.50/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.50/0.70  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.50/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.50/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.50/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.50/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.50/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.70  thf(t65_funct_1, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.70       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.50/0.70  thf('0', plain,
% 0.50/0.70      (![X2 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X2)
% 0.50/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.50/0.70          | ~ (v1_funct_1 @ X2)
% 0.50/0.70          | ~ (v1_relat_1 @ X2))),
% 0.50/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.70  thf(d3_struct_0, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.50/0.70  thf('1', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('2', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf(t64_tops_2, conjecture,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( l1_struct_0 @ A ) =>
% 0.50/0.70       ( ![B:$i]:
% 0.50/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.50/0.70           ( ![C:$i]:
% 0.50/0.70             ( ( ( v1_funct_1 @ C ) & 
% 0.50/0.70                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.50/0.70                 ( m1_subset_1 @
% 0.50/0.70                   C @ 
% 0.50/0.70                   ( k1_zfmisc_1 @
% 0.50/0.70                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.50/0.70               ( ( ( ( k2_relset_1 @
% 0.50/0.70                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.50/0.70                     ( k2_struct_0 @ B ) ) & 
% 0.50/0.70                   ( v2_funct_1 @ C ) ) =>
% 0.50/0.70                 ( r2_funct_2 @
% 0.50/0.70                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.50/0.70                   ( k2_tops_2 @
% 0.50/0.70                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.50/0.70                     ( k2_tops_2 @
% 0.50/0.70                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.50/0.70                   C ) ) ) ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.70    (~( ![A:$i]:
% 0.50/0.70        ( ( l1_struct_0 @ A ) =>
% 0.50/0.70          ( ![B:$i]:
% 0.50/0.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.50/0.70              ( ![C:$i]:
% 0.50/0.70                ( ( ( v1_funct_1 @ C ) & 
% 0.50/0.70                    ( v1_funct_2 @
% 0.50/0.70                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.50/0.70                    ( m1_subset_1 @
% 0.50/0.70                      C @ 
% 0.50/0.70                      ( k1_zfmisc_1 @
% 0.50/0.70                        ( k2_zfmisc_1 @
% 0.50/0.70                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.50/0.70                  ( ( ( ( k2_relset_1 @
% 0.50/0.70                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.50/0.70                        ( k2_struct_0 @ B ) ) & 
% 0.50/0.70                      ( v2_funct_1 @ C ) ) =>
% 0.50/0.70                    ( r2_funct_2 @
% 0.50/0.70                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.50/0.70                      ( k2_tops_2 @
% 0.50/0.70                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.50/0.70                        ( k2_tops_2 @
% 0.50/0.70                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.50/0.70                      C ) ) ) ) ) ) ) )),
% 0.50/0.70    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.50/0.70  thf('3', plain,
% 0.50/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.50/0.70          sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('4', plain,
% 0.50/0.70      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.70           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.50/0.70           sk_C)
% 0.50/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.70  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('6', plain,
% 0.50/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.70          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.50/0.70          sk_C)),
% 0.50/0.70      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.70  thf('7', plain,
% 0.50/0.70      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.70           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.50/0.70           sk_C)
% 0.50/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup-', [status(thm)], ['1', '6'])).
% 0.50/0.70  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('9', plain,
% 0.50/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.70          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.50/0.70          sk_C)),
% 0.50/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.50/0.70  thf('10', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('11', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('12', plain,
% 0.50/0.70      (((m1_subset_1 @ sk_C @ 
% 0.50/0.70         (k1_zfmisc_1 @ 
% 0.50/0.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.50/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['10', '11'])).
% 0.50/0.70  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('14', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.50/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.50/0.70  thf('15', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.50/0.70  thf('16', plain,
% 0.50/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.50/0.70         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.50/0.70          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.50/0.70  thf('17', plain,
% 0.50/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.50/0.70         = (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.50/0.70  thf('18', plain,
% 0.50/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.50/0.70         = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('19', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('20', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.50/0.70      inference('demod', [status(thm)], ['14', '19'])).
% 0.50/0.70  thf(cc5_funct_2, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.50/0.70       ( ![C:$i]:
% 0.50/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.50/0.70             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.50/0.70  thf('21', plain,
% 0.50/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.50/0.70          | (v1_partfun1 @ X12 @ X13)
% 0.50/0.70          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.50/0.70          | ~ (v1_funct_1 @ X12)
% 0.50/0.70          | (v1_xboole_0 @ X14))),
% 0.50/0.70      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.50/0.70  thf('22', plain,
% 0.50/0.70      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.50/0.70        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.50/0.70  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('24', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('25', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('26', plain,
% 0.50/0.70      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.50/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['24', '25'])).
% 0.50/0.70  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('28', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['26', '27'])).
% 0.50/0.70  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('30', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.50/0.70  thf('31', plain,
% 0.50/0.70      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.50/0.70        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.50/0.70      inference('demod', [status(thm)], ['22', '23', '30'])).
% 0.50/0.70  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('33', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf(fc2_struct_0, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.50/0.70       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.50/0.70  thf('34', plain,
% 0.50/0.70      (![X25 : $i]:
% 0.50/0.70         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.50/0.70          | ~ (l1_struct_0 @ X25)
% 0.50/0.70          | (v2_struct_0 @ X25))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.50/0.70  thf('35', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.50/0.70          | ~ (l1_struct_0 @ X0)
% 0.50/0.70          | (v2_struct_0 @ X0)
% 0.50/0.70          | ~ (l1_struct_0 @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.50/0.70  thf('36', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_struct_0 @ X0)
% 0.50/0.70          | ~ (l1_struct_0 @ X0)
% 0.50/0.70          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.50/0.70      inference('simplify', [status(thm)], ['35'])).
% 0.50/0.70  thf('37', plain,
% 0.50/0.70      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.50/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.50/0.70        | (v2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup-', [status(thm)], ['32', '36'])).
% 0.50/0.70  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('39', plain,
% 0.50/0.70      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['37', '38'])).
% 0.50/0.70  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('41', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('clc', [status(thm)], ['39', '40'])).
% 0.50/0.70  thf('42', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('clc', [status(thm)], ['31', '41'])).
% 0.50/0.70  thf(d4_partfun1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.50/0.70       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.50/0.70  thf('43', plain,
% 0.50/0.70      (![X15 : $i, X16 : $i]:
% 0.50/0.70         (~ (v1_partfun1 @ X16 @ X15)
% 0.50/0.70          | ((k1_relat_1 @ X16) = (X15))
% 0.50/0.70          | ~ (v4_relat_1 @ X16 @ X15)
% 0.50/0.70          | ~ (v1_relat_1 @ X16))),
% 0.50/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.50/0.70  thf('44', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.50/0.70        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.70  thf('45', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(cc1_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( v1_relat_1 @ C ) ))).
% 0.50/0.70  thf('46', plain,
% 0.50/0.70      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.70         ((v1_relat_1 @ X3)
% 0.50/0.70          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.50/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.70  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('48', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(cc2_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.50/0.70  thf('49', plain,
% 0.50/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.70         ((v4_relat_1 @ X6 @ X7)
% 0.50/0.70          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.50/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.70  thf('50', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.50/0.70  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['44', '47', '50'])).
% 0.50/0.70  thf('52', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('53', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('clc', [status(thm)], ['31', '41'])).
% 0.50/0.70  thf('54', plain,
% 0.50/0.70      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup+', [status(thm)], ['52', '53'])).
% 0.50/0.70  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('56', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['54', '55'])).
% 0.50/0.70  thf('57', plain,
% 0.50/0.70      (![X15 : $i, X16 : $i]:
% 0.50/0.70         (~ (v1_partfun1 @ X16 @ X15)
% 0.50/0.70          | ((k1_relat_1 @ X16) = (X15))
% 0.50/0.70          | ~ (v4_relat_1 @ X16 @ X15)
% 0.50/0.70          | ~ (v1_relat_1 @ X16))),
% 0.50/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.50/0.70  thf('58', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.50/0.70        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.50/0.70  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('60', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('61', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('62', plain,
% 0.50/0.70      (((m1_subset_1 @ sk_C @ 
% 0.50/0.70         (k1_zfmisc_1 @ 
% 0.50/0.70          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.50/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup+', [status(thm)], ['60', '61'])).
% 0.50/0.70  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('64', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.70  thf('65', plain,
% 0.50/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.70         ((v4_relat_1 @ X6 @ X7)
% 0.50/0.70          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.50/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.70  thf('66', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['64', '65'])).
% 0.50/0.70  thf('67', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['58', '59', '66'])).
% 0.50/0.70  thf('68', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['51', '67'])).
% 0.50/0.70  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('70', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['51', '67'])).
% 0.50/0.70  thf('71', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['51', '67'])).
% 0.50/0.70  thf('72', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('73', plain,
% 0.50/0.70      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.70          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.50/0.70          sk_C)),
% 0.50/0.70      inference('demod', [status(thm)], ['9', '68', '69', '70', '71', '72'])).
% 0.50/0.70  thf('74', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('75', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.70  thf('76', plain,
% 0.50/0.70      (((m1_subset_1 @ sk_C @ 
% 0.50/0.70         (k1_zfmisc_1 @ 
% 0.50/0.70          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.50/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['74', '75'])).
% 0.50/0.70  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('78', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.50/0.70      inference('demod', [status(thm)], ['76', '77'])).
% 0.50/0.70  thf('79', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('80', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.50/0.70      inference('demod', [status(thm)], ['78', '79'])).
% 0.50/0.70  thf(d4_tops_2, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.70       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.50/0.70         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.50/0.70  thf('81', plain,
% 0.50/0.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.70         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.50/0.70          | ~ (v2_funct_1 @ X28)
% 0.50/0.70          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.50/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.50/0.70          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.50/0.70          | ~ (v1_funct_1 @ X28))),
% 0.50/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.50/0.70  thf('82', plain,
% 0.50/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.50/0.70        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70            = (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.70        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70            != (k2_relat_1 @ sk_C)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['80', '81'])).
% 0.50/0.70  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('84', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('85', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('86', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('87', plain,
% 0.50/0.70      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup+', [status(thm)], ['85', '86'])).
% 0.50/0.70  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('89', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.50/0.70  thf('90', plain,
% 0.50/0.70      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.50/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['84', '89'])).
% 0.50/0.70  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('92', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['90', '91'])).
% 0.50/0.70  thf('93', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('94', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['92', '93'])).
% 0.50/0.70  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('96', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('97', plain,
% 0.50/0.70      (![X24 : $i]:
% 0.50/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.70  thf('98', plain,
% 0.50/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.50/0.70         = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('99', plain,
% 0.50/0.70      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.50/0.70          = (k2_struct_0 @ sk_B))
% 0.50/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup+', [status(thm)], ['97', '98'])).
% 0.50/0.70  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('101', plain,
% 0.50/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.50/0.70         = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['99', '100'])).
% 0.50/0.70  thf('102', plain,
% 0.50/0.70      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.50/0.70          = (k2_struct_0 @ sk_B))
% 0.50/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['96', '101'])).
% 0.50/0.70  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('104', plain,
% 0.50/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.50/0.70         = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['102', '103'])).
% 0.50/0.70  thf('105', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('106', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf('107', plain,
% 0.50/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70         = (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.50/0.70  thf('108', plain,
% 0.50/0.70      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70          = (k2_funct_1 @ sk_C))
% 0.50/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.50/0.70      inference('demod', [status(thm)], ['82', '83', '94', '95', '107'])).
% 0.50/0.70  thf('109', plain,
% 0.50/0.70      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70         = (k2_funct_1 @ sk_C))),
% 0.50/0.70      inference('simplify', [status(thm)], ['108'])).
% 0.50/0.70  thf('110', plain,
% 0.50/0.70      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.70          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70           (k2_funct_1 @ sk_C)) @ 
% 0.50/0.70          sk_C)),
% 0.50/0.70      inference('demod', [status(thm)], ['73', '109'])).
% 0.50/0.70  thf(fc6_funct_1, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.50/0.70       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.50/0.70         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.50/0.70         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.50/0.70  thf('111', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('112', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.50/0.70      inference('demod', [status(thm)], ['78', '79'])).
% 0.50/0.70  thf(t31_funct_2, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.50/0.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.50/0.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.50/0.70           ( m1_subset_1 @
% 0.50/0.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.50/0.70  thf('113', plain,
% 0.50/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X21)
% 0.50/0.70          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.50/0.70          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.50/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.50/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.50/0.70          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.50/0.70          | ~ (v1_funct_1 @ X21))),
% 0.50/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.50/0.70  thf('114', plain,
% 0.50/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.50/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.70           (k1_zfmisc_1 @ 
% 0.50/0.70            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.50/0.70        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70            != (k2_relat_1 @ sk_C))
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.70      inference('sup-', [status(thm)], ['112', '113'])).
% 0.50/0.70  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('116', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['92', '93'])).
% 0.50/0.70  thf('117', plain,
% 0.50/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70         = (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.50/0.70  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('119', plain,
% 0.50/0.70      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.70         (k1_zfmisc_1 @ 
% 0.50/0.70          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.50/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.50/0.70      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 0.50/0.70  thf('120', plain,
% 0.50/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.50/0.70      inference('simplify', [status(thm)], ['119'])).
% 0.50/0.70  thf('121', plain,
% 0.50/0.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.70         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.50/0.70          | ~ (v2_funct_1 @ X28)
% 0.50/0.70          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.50/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.50/0.70          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.50/0.70          | ~ (v1_funct_1 @ X28))),
% 0.50/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.50/0.70  thf('122', plain,
% 0.50/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.50/0.70             (k2_struct_0 @ sk_A))
% 0.50/0.70        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.50/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['120', '121'])).
% 0.50/0.70  thf('123', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.50/0.70      inference('demod', [status(thm)], ['78', '79'])).
% 0.50/0.70  thf('124', plain,
% 0.50/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X21)
% 0.50/0.70          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.50/0.70          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.50/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.50/0.70          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.50/0.70          | ~ (v1_funct_1 @ X21))),
% 0.50/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.50/0.70  thf('125', plain,
% 0.50/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.50/0.70        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70            != (k2_relat_1 @ sk_C))
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.70      inference('sup-', [status(thm)], ['123', '124'])).
% 0.50/0.70  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('127', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['92', '93'])).
% 0.50/0.70  thf('128', plain,
% 0.50/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70         = (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.50/0.70  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('130', plain,
% 0.50/0.70      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.50/0.70      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 0.50/0.70  thf('131', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.70      inference('simplify', [status(thm)], ['130'])).
% 0.50/0.70  thf('132', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.50/0.70      inference('demod', [status(thm)], ['78', '79'])).
% 0.50/0.70  thf('133', plain,
% 0.50/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X21)
% 0.50/0.70          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.50/0.70          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.50/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.50/0.70          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.50/0.70          | ~ (v1_funct_1 @ X21))),
% 0.50/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.50/0.70  thf('134', plain,
% 0.50/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.50/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.50/0.70           (k2_struct_0 @ sk_A))
% 0.50/0.70        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70            != (k2_relat_1 @ sk_C))
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.70      inference('sup-', [status(thm)], ['132', '133'])).
% 0.50/0.70  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('136', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['92', '93'])).
% 0.50/0.70  thf('137', plain,
% 0.50/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.50/0.70         = (k2_relat_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.50/0.70  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('139', plain,
% 0.50/0.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.50/0.70         (k2_struct_0 @ sk_A))
% 0.50/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.50/0.70      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 0.50/0.70  thf('140', plain,
% 0.50/0.70      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.50/0.70        (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('simplify', [status(thm)], ['139'])).
% 0.50/0.70  thf('141', plain,
% 0.50/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.50/0.70      inference('simplify', [status(thm)], ['119'])).
% 0.50/0.70  thf('142', plain,
% 0.50/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.50/0.70         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.50/0.70          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.50/0.70  thf('143', plain,
% 0.50/0.70      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['141', '142'])).
% 0.50/0.70  thf('144', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('145', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('146', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('147', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('148', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('149', plain,
% 0.50/0.70      (![X2 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X2)
% 0.50/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.50/0.70          | ~ (v1_funct_1 @ X2)
% 0.50/0.70          | ~ (v1_relat_1 @ X2))),
% 0.50/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.70  thf(t55_funct_1, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.70       ( ( v2_funct_1 @ A ) =>
% 0.50/0.70         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.50/0.70           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.50/0.70  thf('150', plain,
% 0.50/0.70      (![X1 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X1)
% 0.50/0.70          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.50/0.70          | ~ (v1_funct_1 @ X1)
% 0.50/0.70          | ~ (v1_relat_1 @ X1))),
% 0.50/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.50/0.70  thf('151', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.70      inference('sup+', [status(thm)], ['149', '150'])).
% 0.50/0.70  thf('152', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['148', '151'])).
% 0.50/0.70  thf('153', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('simplify', [status(thm)], ['152'])).
% 0.50/0.70  thf('154', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['147', '153'])).
% 0.50/0.70  thf('155', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('simplify', [status(thm)], ['154'])).
% 0.50/0.70  thf('156', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['146', '155'])).
% 0.50/0.70  thf('157', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('simplify', [status(thm)], ['156'])).
% 0.50/0.70  thf('158', plain,
% 0.50/0.70      (![X2 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X2)
% 0.50/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.50/0.70          | ~ (v1_funct_1 @ X2)
% 0.50/0.70          | ~ (v1_relat_1 @ X2))),
% 0.50/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.70  thf('159', plain,
% 0.50/0.70      (![X2 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X2)
% 0.50/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.50/0.70          | ~ (v1_funct_1 @ X2)
% 0.50/0.70          | ~ (v1_relat_1 @ X2))),
% 0.50/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.70  thf('160', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('161', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('162', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('163', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['58', '59', '66'])).
% 0.50/0.70  thf('164', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.50/0.70  thf('165', plain,
% 0.50/0.70      (![X1 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X1)
% 0.50/0.70          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.50/0.70          | ~ (v1_funct_1 @ X1)
% 0.50/0.70          | ~ (v1_relat_1 @ X1))),
% 0.50/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.50/0.70  thf('166', plain,
% 0.50/0.70      (![X2 : $i]:
% 0.50/0.70         (~ (v2_funct_1 @ X2)
% 0.50/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.50/0.70          | ~ (v1_funct_1 @ X2)
% 0.50/0.70          | ~ (v1_relat_1 @ X2))),
% 0.50/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.70  thf('167', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('simplify', [status(thm)], ['156'])).
% 0.50/0.70  thf('168', plain,
% 0.50/0.70      (![X15 : $i, X16 : $i]:
% 0.50/0.70         (((k1_relat_1 @ X16) != (X15))
% 0.50/0.70          | (v1_partfun1 @ X16 @ X15)
% 0.50/0.70          | ~ (v4_relat_1 @ X16 @ X15)
% 0.50/0.70          | ~ (v1_relat_1 @ X16))),
% 0.50/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.50/0.70  thf('169', plain,
% 0.50/0.70      (![X16 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ X16)
% 0.50/0.70          | ~ (v4_relat_1 @ X16 @ (k1_relat_1 @ X16))
% 0.50/0.70          | (v1_partfun1 @ X16 @ (k1_relat_1 @ X16)))),
% 0.50/0.70      inference('simplify', [status(thm)], ['168'])).
% 0.50/0.70  thf('170', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.50/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['167', '169'])).
% 0.50/0.70  thf('171', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.50/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['166', '170'])).
% 0.50/0.70  thf('172', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.50/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.50/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['165', '171'])).
% 0.50/0.70  thf('173', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.50/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.50/0.70      inference('simplify', [status(thm)], ['172'])).
% 0.50/0.70  thf('174', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.50/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['164', '173'])).
% 0.50/0.70  thf('175', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.50/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.50/0.70          | ~ (v2_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_relat_1 @ X0)
% 0.50/0.70          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.50/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.70      inference('simplify', [status(thm)], ['174'])).
% 0.50/0.70  thf('176', plain,
% 0.50/0.70      ((~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.50/0.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.70        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.50/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['163', '175'])).
% 0.50/0.70  thf('177', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['64', '65'])).
% 0.50/0.70  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('181', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.50/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.50/0.70      inference('demod', [status(thm)], ['176', '177', '178', '179', '180'])).
% 0.50/0.70  thf('182', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.70        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.50/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.50/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['162', '181'])).
% 0.50/0.70  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('186', plain,
% 0.50/0.70      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.50/0.70         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.50/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.70      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 0.50/0.70  thf('187', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.50/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['161', '186'])).
% 0.50/0.70  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('191', plain,
% 0.50/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.50/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.50/0.70      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 0.50/0.70  thf('192', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.70        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.50/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['160', '191'])).
% 0.50/0.70  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('195', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('196', plain,
% 0.50/0.70      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.50/0.70        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.70      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 0.50/0.70  thf('197', plain,
% 0.50/0.70      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.50/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.70      inference('sup+', [status(thm)], ['159', '196'])).
% 0.50/0.70  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('201', plain,
% 0.50/0.70      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.70      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 0.50/0.70  thf('202', plain,
% 0.50/0.70      (![X15 : $i, X16 : $i]:
% 0.50/0.70         (~ (v1_partfun1 @ X16 @ X15)
% 0.50/0.70          | ((k1_relat_1 @ X16) = (X15))
% 0.50/0.70          | ~ (v4_relat_1 @ X16 @ X15)
% 0.50/0.70          | ~ (v1_relat_1 @ X16))),
% 0.50/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.50/0.70  thf('203', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v4_relat_1 @ sk_C @ 
% 0.50/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.50/0.70        | ((k1_relat_1 @ sk_C)
% 0.50/0.70            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['201', '202'])).
% 0.50/0.70  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('205', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['58', '59', '66'])).
% 0.50/0.70  thf('206', plain,
% 0.50/0.70      ((~ (v4_relat_1 @ sk_C @ 
% 0.50/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.50/0.70        | ((k2_struct_0 @ sk_A)
% 0.50/0.70            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.50/0.70      inference('demod', [status(thm)], ['203', '204', '205'])).
% 0.50/0.70  thf('207', plain,
% 0.50/0.70      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.50/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.70        | ((k2_struct_0 @ sk_A)
% 0.50/0.70            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['158', '206'])).
% 0.50/0.70  thf('208', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['58', '59', '66'])).
% 0.50/0.70  thf('209', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['64', '65'])).
% 0.50/0.70  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('213', plain,
% 0.50/0.70      (((k2_struct_0 @ sk_A)
% 0.50/0.70         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.70      inference('demod', [status(thm)],
% 0.50/0.70                ['207', '208', '209', '210', '211', '212'])).
% 0.50/0.70  thf('214', plain,
% 0.50/0.70      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.50/0.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.70      inference('sup+', [status(thm)], ['157', '213'])).
% 0.50/0.70  thf('215', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.70      inference('simplify', [status(thm)], ['130'])).
% 0.50/0.70  thf('216', plain,
% 0.50/0.70      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.50/0.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.70      inference('demod', [status(thm)], ['214', '215'])).
% 0.50/0.70  thf('217', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['145', '216'])).
% 0.50/0.70  thf('218', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('220', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('221', plain,
% 0.50/0.70      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.70      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 0.50/0.70  thf('222', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.70        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['144', '221'])).
% 0.50/0.70  thf('223', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('224', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('225', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('226', plain,
% 0.50/0.70      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.70      inference('demod', [status(thm)], ['222', '223', '224', '225'])).
% 0.50/0.70  thf('227', plain,
% 0.50/0.70      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['143', '226'])).
% 0.50/0.70  thf('228', plain,
% 0.50/0.70      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.50/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.50/0.70      inference('demod', [status(thm)], ['122', '131', '140', '227'])).
% 0.50/0.70  thf('229', plain,
% 0.50/0.70      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.70        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.70      inference('simplify', [status(thm)], ['228'])).
% 0.50/0.70  thf('230', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.70        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['111', '229'])).
% 0.50/0.70  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('234', plain,
% 0.50/0.70      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.50/0.70         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.70      inference('demod', [status(thm)], ['230', '231', '232', '233'])).
% 0.50/0.70  thf('235', plain,
% 0.50/0.70      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.70          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.50/0.70      inference('demod', [status(thm)], ['110', '234'])).
% 0.50/0.70  thf('236', plain,
% 0.50/0.70      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.50/0.70           sk_C)
% 0.50/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.70      inference('sup-', [status(thm)], ['0', '235'])).
% 0.50/0.70  thf('237', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('238', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('239', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('240', plain,
% 0.50/0.70      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.50/0.70          sk_C)),
% 0.50/0.70      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 0.50/0.70  thf('241', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.70  thf('242', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_C @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.50/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.70  thf(reflexivity_r2_funct_2, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.50/0.70         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.70       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.50/0.70  thf('243', plain,
% 0.50/0.70      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.50/0.70         ((r2_funct_2 @ X17 @ X18 @ X19 @ X19)
% 0.50/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.50/0.70          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.50/0.70          | ~ (v1_funct_1 @ X19)
% 0.50/0.70          | ~ (v1_funct_1 @ X20)
% 0.50/0.70          | ~ (v1_funct_2 @ X20 @ X17 @ X18)
% 0.50/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.50/0.70      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.50/0.70  thf('244', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.50/0.70             (k1_zfmisc_1 @ 
% 0.50/0.70              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.50/0.70          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.70          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.50/0.70             sk_C))),
% 0.50/0.70      inference('sup-', [status(thm)], ['242', '243'])).
% 0.50/0.70  thf('245', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('246', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.50/0.70  thf('247', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.50/0.70             (k1_zfmisc_1 @ 
% 0.50/0.70              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.50/0.70          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.50/0.70          | ~ (v1_funct_1 @ X0)
% 0.50/0.70          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.50/0.70             sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['244', '245', '246'])).
% 0.50/0.70  thf('248', plain,
% 0.50/0.70      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.70        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['241', '247'])).
% 0.50/0.70  thf('249', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('250', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.50/0.70  thf('251', plain,
% 0.50/0.70      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.50/0.70      inference('demod', [status(thm)], ['248', '249', '250'])).
% 0.50/0.70  thf('252', plain, ($false), inference('demod', [status(thm)], ['240', '251'])).
% 0.50/0.70  
% 0.50/0.70  % SZS output end Refutation
% 0.50/0.70  
% 0.50/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
