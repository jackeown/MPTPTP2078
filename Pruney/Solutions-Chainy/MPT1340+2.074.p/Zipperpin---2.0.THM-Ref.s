%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mSMvb7qpjW

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:19 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  298 (2391 expanded)
%              Number of leaves         :   39 ( 705 expanded)
%              Depth                    :   42
%              Number of atoms          : 2689 (51514 expanded)
%              Number of equality atoms :  113 (1481 expanded)
%              Maximal formula depth    :   16 (   6 average)

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

thf('2',plain,(
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

thf('3',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
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
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('54',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','41'])).

thf('56',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('62',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','68'])).

thf('70',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('72',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','69'])).

thf('73',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

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

thf('75',plain,(
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

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('85',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77','82','83','86'])).

thf('88',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['91'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('93',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('94',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

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

thf('101',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('106',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('112',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    inference('sup+',[status(thm)],['17','18'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('122',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103','110','122','123'])).

thf('125',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
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

thf('127',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('129',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('130',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('133',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('134',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','131','132','133','134'])).

thf('136',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('138',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X22 ) @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('142',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('143',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('147',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('148',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('149',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('150',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('151',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('152',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('153',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('154',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('155',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('156',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
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
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
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
    inference('sup-',[status(thm)],['153','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['152','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('165',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('166',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('167',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','68'])).

thf('168',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('169',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('170',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('172',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != X16 )
      | ( v1_partfun1 @ X17 @ X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('173',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v4_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
      | ( v1_partfun1 @ X17 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['171','173'])).

thf('175',plain,(
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
    inference('sup-',[status(thm)],['170','174'])).

thf('176',plain,(
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
    inference('sup-',[status(thm)],['169','175'])).

thf('177',plain,(
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
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
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
    inference('sup-',[status(thm)],['168','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['167','179'])).

thf('181',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

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
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['166','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['165','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['135'])).

thf('197',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['164','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

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
    inference('sup+',[status(thm)],['163','202'])).

thf('204',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['135'])).

thf('205',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['151','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('208',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['206','207','208','209'])).

thf('211',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['150','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['211','212','213','214'])).

thf('216',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('217',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('219',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','68'])).

thf('220',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['149','220'])).

thf('222',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','68'])).

thf('223',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['221','222','223','224','225','226'])).

thf('228',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['148','227'])).

thf('229',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','136','145','228'])).

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
    inference('sup-',[status(thm)],['93','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

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
    inference(demod,[status(thm)],['9','70','71','72','92','235'])).

thf('237',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','236'])).

thf('238',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['237','238','239','240'])).

thf('242',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('243',plain,(
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

thf('244',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_funct_2 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['245','246','247'])).

thf('249',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','69'])).

thf('250',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','69'])).

thf('251',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','69'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['248','249','250','251'])).

thf('253',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['242','252'])).

thf('254',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('256',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,(
    $false ),
    inference(demod,[status(thm)],['241','256'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mSMvb7qpjW
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 425 iterations in 0.181s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.64  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.64  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.64  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(t65_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      (![X6 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X6)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.45/0.64          | ~ (v1_funct_1 @ X6)
% 0.45/0.64          | ~ (v1_relat_1 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf(d3_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
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
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.64  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '6'])).
% 0.45/0.64  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.45/0.64          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('19', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['14', '19'])).
% 0.45/0.64  thf(cc5_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.64       ( ![C:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.64             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.45/0.64          | (v1_partfun1 @ X13 @ X14)
% 0.45/0.64          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.45/0.64          | ~ (v1_funct_1 @ X13)
% 0.45/0.64          | (v1_xboole_0 @ X15))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.64  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '23', '30'])).
% 0.45/0.64  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf(fc2_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.64       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X26 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.45/0.64          | ~ (l1_struct_0 @ X26)
% 0.45/0.64          | (v2_struct_0 @ X26))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.64          | ~ (l1_struct_0 @ X0)
% 0.45/0.64          | (v2_struct_0 @ X0)
% 0.45/0.64          | ~ (l1_struct_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_struct_0 @ X0)
% 0.45/0.64          | ~ (l1_struct_0 @ X0)
% 0.45/0.64          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.64        | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['32', '36'])).
% 0.45/0.64  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.64  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('41', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('clc', [status(thm)], ['39', '40'])).
% 0.45/0.64  thf('42', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['31', '41'])).
% 0.45/0.64  thf(d4_partfun1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.64       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X17 @ X16)
% 0.45/0.64          | ((k1_relat_1 @ X17) = (X16))
% 0.45/0.64          | ~ (v4_relat_1 @ X17 @ X16)
% 0.45/0.64          | ~ (v1_relat_1 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc2_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ 
% 0.45/0.64           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.64        | (v1_relat_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf(fc6_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.64  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X7 @ X8)
% 0.45/0.64          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('52', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('53', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '49', '52'])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('55', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['31', '41'])).
% 0.45/0.64  thf('56', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['54', '55'])).
% 0.45/0.64  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('58', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X17 @ X16)
% 0.45/0.64          | ((k1_relat_1 @ X17) = (X16))
% 0.45/0.64          | ~ (v4_relat_1 @ X17 @ X16)
% 0.45/0.64          | ~ (v1_relat_1 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('60', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.64  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('62', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('63', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('64', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['62', '63'])).
% 0.45/0.64  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X7 @ X8)
% 0.45/0.64          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('68', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.64  thf('69', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['60', '61', '68'])).
% 0.45/0.64  thf('70', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['53', '69'])).
% 0.45/0.64  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('72', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['53', '69'])).
% 0.45/0.64  thf('73', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('74', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.64  thf(d4_tops_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.64         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.64  thf('75', plain,
% 0.45/0.64      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.45/0.64          | ~ (v2_funct_1 @ X29)
% 0.45/0.64          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.45/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.45/0.64          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.45/0.64          | ~ (v1_funct_1 @ X29))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.64  thf('76', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            != (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.64  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('78', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('79', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('80', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['78', '79'])).
% 0.45/0.64  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('82', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.64  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('84', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.64  thf('85', plain,
% 0.45/0.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.45/0.64          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('86', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.64  thf('87', plain,
% 0.45/0.64      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['76', '77', '82', '83', '86'])).
% 0.45/0.64  thf('88', plain,
% 0.45/0.64      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['73', '87'])).
% 0.45/0.64  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('91', plain,
% 0.45/0.64      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.45/0.64  thf('92', plain,
% 0.45/0.64      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['91'])).
% 0.45/0.64  thf(fc6_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.64         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.64         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.64  thf('93', plain,
% 0.45/0.64      (![X4 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.45/0.64          | ~ (v2_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_relat_1 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('94', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('95', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.64  thf('96', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['94', '95'])).
% 0.45/0.64  thf('97', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('98', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['96', '97'])).
% 0.45/0.64  thf('99', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('100', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['98', '99'])).
% 0.45/0.64  thf(t31_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.64         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.64           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.64           ( m1_subset_1 @
% 0.45/0.64             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('101', plain,
% 0.45/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X22)
% 0.45/0.64          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.45/0.64          | (m1_subset_1 @ (k2_funct_1 @ X22) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.45/0.64          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.45/0.64          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.45/0.64          | ~ (v1_funct_1 @ X22))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('102', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64           (k1_zfmisc_1 @ 
% 0.45/0.64            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['100', '101'])).
% 0.45/0.64  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('104', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('105', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.64  thf('106', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['104', '105'])).
% 0.45/0.64  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('108', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['106', '107'])).
% 0.45/0.64  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('110', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['108', '109'])).
% 0.45/0.64  thf('111', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('112', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('113', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('114', plain,
% 0.45/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['112', '113'])).
% 0.45/0.64  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('116', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['114', '115'])).
% 0.45/0.64  thf('117', plain,
% 0.45/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['111', '116'])).
% 0.45/0.64  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('119', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['117', '118'])).
% 0.45/0.64  thf('120', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('121', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('122', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.45/0.64  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('124', plain,
% 0.45/0.64      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['102', '103', '110', '122', '123'])).
% 0.45/0.64  thf('125', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['124'])).
% 0.45/0.64  thf('126', plain,
% 0.45/0.64      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.45/0.64          | ~ (v2_funct_1 @ X29)
% 0.45/0.64          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.45/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.45/0.64          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.45/0.64          | ~ (v1_funct_1 @ X29))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.64  thf('127', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64             (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['125', '126'])).
% 0.45/0.64  thf('128', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['98', '99'])).
% 0.45/0.64  thf('129', plain,
% 0.45/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X22)
% 0.45/0.64          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.45/0.64          | (v1_funct_1 @ (k2_funct_1 @ X22))
% 0.45/0.64          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.45/0.64          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.45/0.64          | ~ (v1_funct_1 @ X22))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('130', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['128', '129'])).
% 0.45/0.64  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('132', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['108', '109'])).
% 0.45/0.64  thf('133', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.45/0.64  thf('134', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('135', plain,
% 0.45/0.64      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['130', '131', '132', '133', '134'])).
% 0.45/0.64  thf('136', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['135'])).
% 0.45/0.64  thf('137', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['98', '99'])).
% 0.45/0.64  thf('138', plain,
% 0.45/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X22)
% 0.45/0.64          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.45/0.64          | (v1_funct_2 @ (k2_funct_1 @ X22) @ X23 @ X24)
% 0.45/0.64          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.45/0.64          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.45/0.64          | ~ (v1_funct_1 @ X22))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('139', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64           (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['137', '138'])).
% 0.45/0.64  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('141', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['108', '109'])).
% 0.45/0.64  thf('142', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.45/0.64  thf('143', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('144', plain,
% 0.45/0.64      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64         (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 0.45/0.64  thf('145', plain,
% 0.45/0.64      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64        (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('simplify', [status(thm)], ['144'])).
% 0.45/0.64  thf('146', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['124'])).
% 0.45/0.64  thf('147', plain,
% 0.45/0.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.45/0.64          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('148', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['146', '147'])).
% 0.45/0.64  thf(t55_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v2_funct_1 @ A ) =>
% 0.45/0.64         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.64           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('149', plain,
% 0.45/0.64      (![X5 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X5)
% 0.45/0.64          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.45/0.64          | ~ (v1_funct_1 @ X5)
% 0.45/0.64          | ~ (v1_relat_1 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('150', plain,
% 0.45/0.64      (![X4 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.45/0.64          | ~ (v2_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_relat_1 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('151', plain,
% 0.45/0.64      (![X4 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.64          | ~ (v2_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_relat_1 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('152', plain,
% 0.45/0.64      (![X4 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.45/0.64          | ~ (v2_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_relat_1 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('153', plain,
% 0.45/0.64      (![X4 : $i]:
% 0.45/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.45/0.64          | ~ (v2_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_relat_1 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('154', plain,
% 0.45/0.64      (![X4 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.64          | ~ (v2_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_relat_1 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('155', plain,
% 0.45/0.64      (![X6 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X6)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.45/0.64          | ~ (v1_funct_1 @ X6)
% 0.45/0.64          | ~ (v1_relat_1 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf('156', plain,
% 0.45/0.64      (![X5 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X5)
% 0.45/0.64          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.45/0.64          | ~ (v1_funct_1 @ X5)
% 0.45/0.64          | ~ (v1_relat_1 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('157', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['155', '156'])).
% 0.45/0.64  thf('158', plain,
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
% 0.45/0.64      inference('sup-', [status(thm)], ['154', '157'])).
% 0.45/0.64  thf('159', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['158'])).
% 0.45/0.64  thf('160', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['153', '159'])).
% 0.45/0.64  thf('161', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['160'])).
% 0.45/0.64  thf('162', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['152', '161'])).
% 0.45/0.64  thf('163', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['162'])).
% 0.45/0.64  thf('164', plain,
% 0.45/0.64      (![X6 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X6)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.45/0.64          | ~ (v1_funct_1 @ X6)
% 0.45/0.64          | ~ (v1_relat_1 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf('165', plain,
% 0.45/0.64      (![X4 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.45/0.64          | ~ (v2_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_relat_1 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('166', plain,
% 0.45/0.64      (![X4 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.64          | ~ (v2_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_relat_1 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('167', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['60', '61', '68'])).
% 0.45/0.64  thf('168', plain,
% 0.45/0.64      (![X4 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.64          | ~ (v2_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_funct_1 @ X4)
% 0.45/0.64          | ~ (v1_relat_1 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('169', plain,
% 0.45/0.64      (![X5 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X5)
% 0.45/0.64          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.45/0.64          | ~ (v1_funct_1 @ X5)
% 0.45/0.64          | ~ (v1_relat_1 @ X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('170', plain,
% 0.45/0.64      (![X6 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X6)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.45/0.64          | ~ (v1_funct_1 @ X6)
% 0.45/0.64          | ~ (v1_relat_1 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf('171', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['162'])).
% 0.45/0.64  thf('172', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         (((k1_relat_1 @ X17) != (X16))
% 0.45/0.64          | (v1_partfun1 @ X17 @ X16)
% 0.45/0.64          | ~ (v4_relat_1 @ X17 @ X16)
% 0.45/0.64          | ~ (v1_relat_1 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('173', plain,
% 0.45/0.64      (![X17 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X17)
% 0.45/0.64          | ~ (v4_relat_1 @ X17 @ (k1_relat_1 @ X17))
% 0.45/0.64          | (v1_partfun1 @ X17 @ (k1_relat_1 @ X17)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['172'])).
% 0.45/0.64  thf('174', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['171', '173'])).
% 0.45/0.64  thf('175', plain,
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
% 0.45/0.64      inference('sup-', [status(thm)], ['170', '174'])).
% 0.45/0.64  thf('176', plain,
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
% 0.45/0.64      inference('sup-', [status(thm)], ['169', '175'])).
% 0.45/0.64  thf('177', plain,
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
% 0.45/0.64      inference('simplify', [status(thm)], ['176'])).
% 0.45/0.64  thf('178', plain,
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
% 0.45/0.64      inference('sup-', [status(thm)], ['168', '177'])).
% 0.45/0.64  thf('179', plain,
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
% 0.45/0.64      inference('simplify', [status(thm)], ['178'])).
% 0.45/0.64  thf('180', plain,
% 0.45/0.64      ((~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['167', '179'])).
% 0.45/0.64  thf('181', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.64  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('184', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('185', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 0.45/0.64  thf('186', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['166', '185'])).
% 0.45/0.64  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('190', plain,
% 0.45/0.64      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 0.45/0.64  thf('191', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['165', '190'])).
% 0.45/0.64  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('195', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 0.45/0.64  thf('196', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['135'])).
% 0.45/0.64  thf('197', plain,
% 0.45/0.64      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['195', '196'])).
% 0.45/0.64  thf('198', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup+', [status(thm)], ['164', '197'])).
% 0.45/0.64  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('202', plain,
% 0.45/0.64      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 0.45/0.64  thf('203', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['163', '202'])).
% 0.45/0.64  thf('204', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['135'])).
% 0.45/0.64  thf('205', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['203', '204'])).
% 0.45/0.64  thf('206', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['151', '205'])).
% 0.45/0.64  thf('207', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('208', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('209', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('210', plain,
% 0.45/0.64      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['206', '207', '208', '209'])).
% 0.45/0.64  thf('211', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['150', '210'])).
% 0.45/0.64  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('215', plain,
% 0.45/0.64      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['211', '212', '213', '214'])).
% 0.45/0.64  thf('216', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X17 @ X16)
% 0.45/0.64          | ((k1_relat_1 @ X17) = (X16))
% 0.45/0.64          | ~ (v4_relat_1 @ X17 @ X16)
% 0.45/0.64          | ~ (v1_relat_1 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('217', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['215', '216'])).
% 0.45/0.64  thf('218', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('219', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['60', '61', '68'])).
% 0.45/0.64  thf('220', plain,
% 0.45/0.64      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['217', '218', '219'])).
% 0.45/0.64  thf('221', plain,
% 0.45/0.64      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['149', '220'])).
% 0.45/0.64  thf('222', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['60', '61', '68'])).
% 0.45/0.64  thf('223', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.64  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('226', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('227', plain,
% 0.45/0.64      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)],
% 0.45/0.64                ['221', '222', '223', '224', '225', '226'])).
% 0.45/0.64  thf('228', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['148', '227'])).
% 0.45/0.64  thf('229', plain,
% 0.45/0.64      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['127', '136', '145', '228'])).
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
% 0.45/0.64      inference('sup-', [status(thm)], ['93', '230'])).
% 0.45/0.64  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
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
% 0.45/0.64      inference('demod', [status(thm)], ['9', '70', '71', '72', '92', '235'])).
% 0.45/0.64  thf('237', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['0', '236'])).
% 0.45/0.64  thf('238', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.64  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('240', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('241', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['237', '238', '239', '240'])).
% 0.45/0.64  thf('242', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.64  thf('243', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(reflexivity_r2_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.64         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.45/0.64  thf('244', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.64         ((r2_funct_2 @ X18 @ X19 @ X20 @ X20)
% 0.45/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.64          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.45/0.64          | ~ (v1_funct_1 @ X20)
% 0.45/0.64          | ~ (v1_funct_1 @ X21)
% 0.45/0.64          | ~ (v1_funct_2 @ X21 @ X18 @ X19)
% 0.45/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.64      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.45/0.64  thf('245', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64             sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['243', '244'])).
% 0.45/0.64  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('247', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('248', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64             sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['245', '246', '247'])).
% 0.45/0.64  thf('249', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['53', '69'])).
% 0.45/0.64  thf('250', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['53', '69'])).
% 0.45/0.64  thf('251', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['53', '69'])).
% 0.45/0.64  thf('252', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64             sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['248', '249', '250', '251'])).
% 0.45/0.64  thf('253', plain,
% 0.45/0.64      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['242', '252'])).
% 0.45/0.64  thf('254', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('255', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.64  thf('256', plain,
% 0.45/0.64      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['253', '254', '255'])).
% 0.45/0.64  thf('257', plain, ($false), inference('demod', [status(thm)], ['241', '256'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
