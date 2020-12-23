%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7lQqVw2DLq

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:05 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  295 (1710 expanded)
%              Number of leaves         :   48 ( 519 expanded)
%              Depth                    :   32
%              Number of atoms          : 2794 (36974 expanded)
%              Number of equality atoms :  141 (1050 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20','23'])).

thf('25',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','37'])).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','51'])).

thf('53',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('54',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('61',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','58','59','60'])).

thf('62',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
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

thf('67',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_tops_2 @ X37 @ X36 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('68',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('72',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69','74','75','84'])).

thf('86',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['61','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

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

thf('89',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('93',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('94',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_tops_2 @ X37 @ X36 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('100',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('109',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X33 @ X32 @ X31 )
       != X32 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X31 ) @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('113',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['115'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('117',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('118',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('119',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('120',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf('121',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('122',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('124',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('134',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('135',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('136',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
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
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['133','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('144',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('146',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('147',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('151',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('152',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['149','155'])).

thf('157',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('158',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('160',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['159'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('161',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X5 @ ( k1_relat_1 @ X6 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X6 ) @ ( k9_relat_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['158','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('167',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','169','170','171','172'])).

thf('174',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('176',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('177',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['176','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['175','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['174','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['173','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['144','190'])).

thf('192',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('194',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','194'])).

thf('196',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['132','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['196','197','198','199'])).

thf('201',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('202',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','169','170','171','172'])).

thf('207',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('208',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('210',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('211',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['202','203','204','205','208','209','210'])).

thf('212',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('218',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('219',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('221',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','107','116','216','221'])).

thf('223',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['87','223'])).

thf('225',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','224'])).

thf('226',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('227',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['225','226','227','228'])).

thf('230',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('231',plain,(
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

thf('232',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_funct_2 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('238',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('239',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['230','240'])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('244',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,(
    $false ),
    inference(demod,[status(thm)],['229','244'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7lQqVw2DLq
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 557 iterations in 0.207s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.67  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.67  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.67  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.67  thf(t65_funct_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (![X12 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X12)
% 0.46/0.67          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.46/0.67          | ~ (v1_funct_1 @ X12)
% 0.46/0.67          | ~ (v1_relat_1 @ X12))),
% 0.46/0.67      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.67  thf(d3_struct_0, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf(t64_tops_2, conjecture,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_struct_0 @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.67           ( ![C:$i]:
% 0.46/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.67                 ( m1_subset_1 @
% 0.46/0.67                   C @ 
% 0.46/0.67                   ( k1_zfmisc_1 @
% 0.46/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.67               ( ( ( ( k2_relset_1 @
% 0.46/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.67                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.67                 ( r2_funct_2 @
% 0.46/0.67                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.67                   ( k2_tops_2 @
% 0.46/0.67                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.67                     ( k2_tops_2 @
% 0.46/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.67                   C ) ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i]:
% 0.46/0.67        ( ( l1_struct_0 @ A ) =>
% 0.46/0.67          ( ![B:$i]:
% 0.46/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.67              ( ![C:$i]:
% 0.46/0.67                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.67                    ( v1_funct_2 @
% 0.46/0.67                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.67                    ( m1_subset_1 @
% 0.46/0.67                      C @ 
% 0.46/0.67                      ( k1_zfmisc_1 @
% 0.46/0.67                        ( k2_zfmisc_1 @
% 0.46/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.67                  ( ( ( ( k2_relset_1 @
% 0.46/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.67                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.67                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.67                    ( r2_funct_2 @
% 0.46/0.67                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.67                      ( k2_tops_2 @
% 0.46/0.67                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.67                        ( k2_tops_2 @
% 0.46/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.67                      C ) ) ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.67          sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.67           sk_C)
% 0.46/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.67          sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.67           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.67           sk_C)
% 0.46/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['1', '6'])).
% 0.46/0.67  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.67          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.67          sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc5_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.67       ( ![C:$i]:
% 0.46/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.67             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.46/0.67          | (v1_partfun1 @ X22 @ X23)
% 0.46/0.67          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.46/0.67          | ~ (v1_funct_1 @ X22)
% 0.46/0.67          | (v1_xboole_0 @ X24))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.67  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.46/0.67  thf(d4_partfun1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.67       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i]:
% 0.46/0.67         (~ (v1_partfun1 @ X26 @ X25)
% 0.46/0.67          | ((k1_relat_1 @ X26) = (X25))
% 0.46/0.67          | ~ (v4_relat_1 @ X26 @ X25)
% 0.46/0.67          | ~ (v1_relat_1 @ X26))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.67        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc1_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( v1_relat_1 @ C ) ))).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.67         ((v1_relat_1 @ X13)
% 0.46/0.67          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.67  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc2_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.67         ((v4_relat_1 @ X16 @ X17)
% 0.46/0.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.67  thf('23', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['17', '20', '23'])).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (((m1_subset_1 @ sk_C @ 
% 0.46/0.67         (k1_zfmisc_1 @ 
% 0.46/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.67  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.46/0.67          | (v1_partfun1 @ X22 @ X23)
% 0.46/0.67          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.46/0.67          | ~ (v1_funct_1 @ X22)
% 0.46/0.67          | (v1_xboole_0 @ X24))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.67  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.67  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['31', '32', '37'])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i]:
% 0.46/0.67         (~ (v1_partfun1 @ X26 @ X25)
% 0.46/0.67          | ((k1_relat_1 @ X26) = (X25))
% 0.46/0.67          | ~ (v4_relat_1 @ X26 @ X25)
% 0.46/0.67          | ~ (v1_relat_1 @ X26))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.67  thf('40', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.67        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.67  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('42', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.67         ((v4_relat_1 @ X16 @ X17)
% 0.46/0.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.67  thf('44', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['40', '41', '44'])).
% 0.46/0.67  thf(fc2_struct_0, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.67       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      (![X35 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X35))
% 0.46/0.67          | ~ (l1_struct_0 @ X35)
% 0.46/0.67          | (v2_struct_0 @ X35))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.46/0.67        | (v2_struct_0 @ sk_B)
% 0.46/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.67  thf('48', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['47', '48'])).
% 0.46/0.67  thf('50', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('51', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['49', '50'])).
% 0.46/0.67  thf('52', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.67        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['24', '51'])).
% 0.46/0.67  thf('53', plain,
% 0.46/0.67      (![X35 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X35))
% 0.46/0.67          | ~ (l1_struct_0 @ X35)
% 0.46/0.67          | (v2_struct_0 @ X35))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.67  thf('54', plain,
% 0.46/0.67      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.46/0.67        | (v2_struct_0 @ sk_B)
% 0.46/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.67  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.67  thf('57', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('58', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['56', '57'])).
% 0.46/0.67  thf('59', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['56', '57'])).
% 0.46/0.67  thf('60', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['56', '57'])).
% 0.46/0.67  thf('61', plain,
% 0.46/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.67          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.67           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.67          sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['9', '58', '59', '60'])).
% 0.46/0.67  thf('62', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('63', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('64', plain,
% 0.46/0.67      (((m1_subset_1 @ sk_C @ 
% 0.46/0.67         (k1_zfmisc_1 @ 
% 0.46/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup+', [status(thm)], ['62', '63'])).
% 0.46/0.67  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('66', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.67  thf(d4_tops_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.67       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.67         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.67  thf('67', plain,
% 0.46/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.67         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 0.46/0.67          | ~ (v2_funct_1 @ X38)
% 0.46/0.67          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 0.46/0.67          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.46/0.67          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.46/0.67          | ~ (v1_funct_1 @ X38))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.67  thf('68', plain,
% 0.46/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.67        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67            = (k2_funct_1 @ sk_C))
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67            != (k2_struct_0 @ sk_B)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.67  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('70', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('71', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.67  thf('72', plain,
% 0.46/0.67      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup+', [status(thm)], ['70', '71'])).
% 0.46/0.67  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('74', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.67  thf('75', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('76', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('77', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('78', plain,
% 0.46/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67         = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('79', plain,
% 0.46/0.67      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67          = (k2_struct_0 @ sk_B))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup+', [status(thm)], ['77', '78'])).
% 0.46/0.67  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('81', plain,
% 0.46/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67         = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['79', '80'])).
% 0.46/0.67  thf('82', plain,
% 0.46/0.67      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67          = (k2_struct_0 @ sk_B))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup+', [status(thm)], ['76', '81'])).
% 0.46/0.67  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('84', plain,
% 0.46/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67         = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['82', '83'])).
% 0.46/0.67  thf('85', plain,
% 0.46/0.67      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67          = (k2_funct_1 @ sk_C))
% 0.46/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['68', '69', '74', '75', '84'])).
% 0.46/0.67  thf('86', plain,
% 0.46/0.67      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67         = (k2_funct_1 @ sk_C))),
% 0.46/0.67      inference('simplify', [status(thm)], ['85'])).
% 0.46/0.67  thf('87', plain,
% 0.46/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.67          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.67           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.67          sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['61', '86'])).
% 0.46/0.67  thf('88', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.67  thf(t31_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.67       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.67         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.67           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.67           ( m1_subset_1 @
% 0.46/0.67             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.67  thf('89', plain,
% 0.46/0.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X31)
% 0.46/0.67          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 0.46/0.67          | (m1_subset_1 @ (k2_funct_1 @ X31) @ 
% 0.46/0.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.46/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.46/0.67          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 0.46/0.67          | ~ (v1_funct_1 @ X31))),
% 0.46/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.67  thf('90', plain,
% 0.46/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.67        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.67           (k1_zfmisc_1 @ 
% 0.46/0.67            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67            != (k2_struct_0 @ sk_B))
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.67  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('92', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.67  thf('93', plain,
% 0.46/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67         = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['82', '83'])).
% 0.46/0.67  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('95', plain,
% 0.46/0.67      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.67         (k1_zfmisc_1 @ 
% 0.46/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 0.46/0.67  thf('96', plain,
% 0.46/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('simplify', [status(thm)], ['95'])).
% 0.46/0.67  thf('97', plain,
% 0.46/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.67         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 0.46/0.67          | ~ (v2_funct_1 @ X38)
% 0.46/0.67          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 0.46/0.67          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.46/0.67          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.46/0.67          | ~ (v1_funct_1 @ X38))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.67  thf('98', plain,
% 0.46/0.67      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.67             (k2_struct_0 @ sk_A))
% 0.46/0.67        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.67            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.67        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.67            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['96', '97'])).
% 0.46/0.67  thf('99', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.67  thf('100', plain,
% 0.46/0.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X31)
% 0.46/0.67          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 0.46/0.67          | (v1_funct_1 @ (k2_funct_1 @ X31))
% 0.46/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.46/0.67          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 0.46/0.67          | ~ (v1_funct_1 @ X31))),
% 0.46/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.67  thf('101', plain,
% 0.46/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.67        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67            != (k2_struct_0 @ sk_B))
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.67  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('103', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.67  thf('104', plain,
% 0.46/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67         = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['82', '83'])).
% 0.46/0.67  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('106', plain,
% 0.46/0.67      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 0.46/0.67  thf('107', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.67      inference('simplify', [status(thm)], ['106'])).
% 0.46/0.67  thf('108', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.67  thf('109', plain,
% 0.46/0.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X31)
% 0.46/0.67          | ((k2_relset_1 @ X33 @ X32 @ X31) != (X32))
% 0.46/0.67          | (v1_funct_2 @ (k2_funct_1 @ X31) @ X32 @ X33)
% 0.46/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.46/0.67          | ~ (v1_funct_2 @ X31 @ X33 @ X32)
% 0.46/0.67          | ~ (v1_funct_1 @ X31))),
% 0.46/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.67  thf('110', plain,
% 0.46/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.67        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.67           (k2_struct_0 @ sk_A))
% 0.46/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67            != (k2_struct_0 @ sk_B))
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['108', '109'])).
% 0.46/0.67  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('112', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.67  thf('113', plain,
% 0.46/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67         = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['82', '83'])).
% 0.46/0.67  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('115', plain,
% 0.46/0.67      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.67         (k2_struct_0 @ sk_A))
% 0.46/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.46/0.67  thf('116', plain,
% 0.46/0.67      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.67        (k2_struct_0 @ sk_A))),
% 0.46/0.67      inference('simplify', [status(thm)], ['115'])).
% 0.46/0.67  thf(dt_k2_funct_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.67         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.67  thf('117', plain,
% 0.46/0.67      (![X4 : $i]:
% 0.46/0.67         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.67          | ~ (v1_funct_1 @ X4)
% 0.46/0.67          | ~ (v1_relat_1 @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.67  thf(t55_funct_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ( v2_funct_1 @ A ) =>
% 0.46/0.67         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.67           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.67  thf('118', plain,
% 0.46/0.67      (![X10 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X10)
% 0.46/0.67          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.67          | ~ (v1_funct_1 @ X10)
% 0.46/0.67          | ~ (v1_relat_1 @ X10))),
% 0.46/0.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.67  thf('119', plain,
% 0.46/0.67      (![X4 : $i]:
% 0.46/0.67         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.67          | ~ (v1_funct_1 @ X4)
% 0.46/0.67          | ~ (v1_relat_1 @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.67  thf('120', plain,
% 0.46/0.67      (![X4 : $i]:
% 0.46/0.67         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.67          | ~ (v1_funct_1 @ X4)
% 0.46/0.67          | ~ (v1_relat_1 @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.67  thf(t61_funct_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ( v2_funct_1 @ A ) =>
% 0.46/0.67         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.46/0.67             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.46/0.67           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.46/0.67             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.67  thf('121', plain,
% 0.46/0.67      (![X11 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X11)
% 0.46/0.67          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 0.46/0.67              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 0.46/0.67          | ~ (v1_funct_1 @ X11)
% 0.46/0.67          | ~ (v1_relat_1 @ X11))),
% 0.46/0.67      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.67  thf(t48_funct_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.67           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.46/0.67               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.67             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.67  thf('122', plain,
% 0.46/0.67      (![X7 : $i, X8 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X7)
% 0.46/0.67          | ~ (v1_funct_1 @ X7)
% 0.46/0.67          | (v2_funct_1 @ X7)
% 0.46/0.67          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.46/0.67          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.46/0.67          | ~ (v1_funct_1 @ X8)
% 0.46/0.67          | ~ (v1_relat_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.46/0.67  thf('123', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.67          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['121', '122'])).
% 0.46/0.67  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.46/0.67  thf('124', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 0.46/0.67      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.46/0.67  thf('125', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.67          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.67      inference('demod', [status(thm)], ['123', '124'])).
% 0.46/0.67  thf('126', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['125'])).
% 0.46/0.67  thf('127', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.67          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['120', '126'])).
% 0.46/0.67  thf('128', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['127'])).
% 0.46/0.67  thf('129', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.67          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['119', '128'])).
% 0.46/0.67  thf('130', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['129'])).
% 0.46/0.67  thf('131', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['118', '130'])).
% 0.46/0.67  thf('132', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['131'])).
% 0.46/0.67  thf('133', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.67      inference('simplify', [status(thm)], ['106'])).
% 0.46/0.67  thf('134', plain,
% 0.46/0.67      (![X4 : $i]:
% 0.46/0.67         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.67          | ~ (v1_funct_1 @ X4)
% 0.46/0.67          | ~ (v1_relat_1 @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.67  thf('135', plain,
% 0.46/0.67      (![X12 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X12)
% 0.46/0.67          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.46/0.67          | ~ (v1_funct_1 @ X12)
% 0.46/0.67          | ~ (v1_relat_1 @ X12))),
% 0.46/0.67      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.67  thf('136', plain,
% 0.46/0.67      (![X11 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X11)
% 0.46/0.67          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 0.46/0.67              = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.46/0.67          | ~ (v1_funct_1 @ X11)
% 0.46/0.67          | ~ (v1_relat_1 @ X11))),
% 0.46/0.67      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.67  thf('137', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.67            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['135', '136'])).
% 0.46/0.67  thf('138', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.67              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['134', '137'])).
% 0.46/0.67  thf('139', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.67            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['138'])).
% 0.46/0.67  thf('140', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.67        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.67            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['133', '139'])).
% 0.46/0.67  thf('141', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('143', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t146_relat_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ A ) =>
% 0.46/0.67       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.46/0.67  thf('144', plain,
% 0.46/0.67      (![X3 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.46/0.67          | ~ (v1_relat_1 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.46/0.67  thf('145', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.67  thf('146', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.67         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.46/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.67  thf('147', plain,
% 0.46/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67         = (k2_relat_1 @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['145', '146'])).
% 0.46/0.67  thf('148', plain,
% 0.46/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.67         = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('149', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup+', [status(thm)], ['147', '148'])).
% 0.46/0.67  thf('150', plain,
% 0.46/0.67      (![X4 : $i]:
% 0.46/0.67         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.67          | ~ (v1_funct_1 @ X4)
% 0.46/0.67          | ~ (v1_relat_1 @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.67  thf('151', plain,
% 0.46/0.67      (![X10 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X10)
% 0.46/0.67          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.67          | ~ (v1_funct_1 @ X10)
% 0.46/0.67          | ~ (v1_relat_1 @ X10))),
% 0.46/0.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.67  thf('152', plain,
% 0.46/0.67      (![X3 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.46/0.67          | ~ (v1_relat_1 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.46/0.67  thf('153', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.67            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['151', '152'])).
% 0.46/0.67  thf('154', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.67              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['150', '153'])).
% 0.46/0.67  thf('155', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.67            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['154'])).
% 0.46/0.67  thf('156', plain,
% 0.46/0.67      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.67          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.67      inference('sup+', [status(thm)], ['149', '155'])).
% 0.46/0.67  thf('157', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup+', [status(thm)], ['147', '148'])).
% 0.46/0.67  thf('158', plain,
% 0.46/0.67      (![X3 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.46/0.67          | ~ (v1_relat_1 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.46/0.67  thf(d10_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.67  thf('159', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.67  thf('160', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.67      inference('simplify', [status(thm)], ['159'])).
% 0.46/0.67  thf(t177_funct_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.67           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.46/0.67             ( B ) ) ) ) ))).
% 0.46/0.67  thf('161', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i]:
% 0.46/0.67         (~ (r1_tarski @ X5 @ (k1_relat_1 @ X6))
% 0.46/0.67          | ((k9_relat_1 @ (k2_funct_1 @ X6) @ (k9_relat_1 @ X6 @ X5)) = (X5))
% 0.46/0.67          | ~ (v2_funct_1 @ X6)
% 0.46/0.67          | ~ (v1_funct_1 @ X6)
% 0.46/0.67          | ~ (v1_relat_1 @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.46/0.67  thf('162', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.46/0.67              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['160', '161'])).
% 0.46/0.67  thf('163', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.67            = (k1_relat_1 @ X0))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['158', '162'])).
% 0.46/0.67  thf('164', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.67              = (k1_relat_1 @ X0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['163'])).
% 0.46/0.67  thf('165', plain,
% 0.46/0.67      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.67          = (k1_relat_1 @ sk_C))
% 0.46/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.67      inference('sup+', [status(thm)], ['157', '164'])).
% 0.46/0.67  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('167', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('169', plain,
% 0.46/0.67      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.67         = (k1_relat_1 @ sk_C))),
% 0.46/0.67      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 0.46/0.67  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('173', plain,
% 0.46/0.67      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('demod', [status(thm)], ['156', '169', '170', '171', '172'])).
% 0.46/0.67  thf('174', plain,
% 0.46/0.67      (![X4 : $i]:
% 0.46/0.67         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.67          | ~ (v1_funct_1 @ X4)
% 0.46/0.67          | ~ (v1_relat_1 @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.67  thf('175', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['131'])).
% 0.46/0.67  thf('176', plain,
% 0.46/0.67      (![X4 : $i]:
% 0.46/0.67         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.67          | ~ (v1_funct_1 @ X4)
% 0.46/0.67          | ~ (v1_relat_1 @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.67  thf('177', plain,
% 0.46/0.67      (![X12 : $i]:
% 0.46/0.67         (~ (v2_funct_1 @ X12)
% 0.46/0.67          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.46/0.67          | ~ (v1_funct_1 @ X12)
% 0.46/0.67          | ~ (v1_relat_1 @ X12))),
% 0.46/0.67      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.67  thf('178', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.67              = (k1_relat_1 @ X0)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['163'])).
% 0.46/0.67  thf('179', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['177', '178'])).
% 0.46/0.67  thf('180', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['176', '179'])).
% 0.46/0.67  thf('181', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['180'])).
% 0.46/0.67  thf('182', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['175', '181'])).
% 0.46/0.67  thf('183', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['182'])).
% 0.46/0.67  thf('184', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['174', '183'])).
% 0.46/0.67  thf('185', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.67          | ~ (v2_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['184'])).
% 0.46/0.67  thf('186', plain,
% 0.46/0.67      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.46/0.67          = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.67      inference('sup+', [status(thm)], ['173', '185'])).
% 0.46/0.67  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('190', plain,
% 0.46/0.67      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.46/0.67         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 0.46/0.67  thf('191', plain,
% 0.46/0.67      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.67        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.67      inference('sup+', [status(thm)], ['144', '190'])).
% 0.46/0.67  thf('192', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup+', [status(thm)], ['147', '148'])).
% 0.46/0.67  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('194', plain,
% 0.46/0.67      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('demod', [status(thm)], ['191', '192', '193'])).
% 0.46/0.67  thf('195', plain,
% 0.46/0.67      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.67            = (k6_relat_1 @ (k2_struct_0 @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['140', '141', '142', '143', '194'])).
% 0.46/0.67  thf('196', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.67        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.67            = (k6_relat_1 @ (k2_struct_0 @ sk_B))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['132', '195'])).
% 0.46/0.67  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('199', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('200', plain,
% 0.46/0.67      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.67         = (k6_relat_1 @ (k2_struct_0 @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['196', '197', '198', '199'])).
% 0.46/0.67  thf('201', plain,
% 0.46/0.67      (![X7 : $i, X8 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X7)
% 0.46/0.67          | ~ (v1_funct_1 @ X7)
% 0.46/0.67          | (v2_funct_1 @ X7)
% 0.46/0.67          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.46/0.67          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.46/0.67          | ~ (v1_funct_1 @ X8)
% 0.46/0.67          | ~ (v1_relat_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.46/0.67  thf('202', plain,
% 0.46/0.67      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_struct_0 @ sk_B)))
% 0.46/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.67        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['200', '201'])).
% 0.46/0.67  thf('203', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 0.46/0.67      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.46/0.67  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('206', plain,
% 0.46/0.67      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('demod', [status(thm)], ['156', '169', '170', '171', '172'])).
% 0.46/0.67  thf('207', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['49', '50'])).
% 0.46/0.67  thf('208', plain,
% 0.46/0.67      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('demod', [status(thm)], ['206', '207'])).
% 0.46/0.67  thf('209', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['49', '50'])).
% 0.46/0.67  thf('210', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.67      inference('simplify', [status(thm)], ['106'])).
% 0.46/0.67  thf('211', plain,
% 0.46/0.67      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.67        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('demod', [status(thm)],
% 0.46/0.67                ['202', '203', '204', '205', '208', '209', '210'])).
% 0.46/0.67  thf('212', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.67        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['211'])).
% 0.46/0.67  thf('213', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['117', '212'])).
% 0.46/0.67  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('216', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.67      inference('demod', [status(thm)], ['213', '214', '215'])).
% 0.46/0.67  thf('217', plain,
% 0.46/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('simplify', [status(thm)], ['95'])).
% 0.46/0.67  thf('218', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.67         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.46/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.67  thf('219', plain,
% 0.46/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.67         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['217', '218'])).
% 0.46/0.67  thf('220', plain,
% 0.46/0.67      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('demod', [status(thm)], ['206', '207'])).
% 0.46/0.67  thf('221', plain,
% 0.46/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.67         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['219', '220'])).
% 0.46/0.67  thf('222', plain,
% 0.46/0.67      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.67          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.67        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['98', '107', '116', '216', '221'])).
% 0.46/0.67  thf('223', plain,
% 0.46/0.67      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.67         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['222'])).
% 0.46/0.67  thf('224', plain,
% 0.46/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.67          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['87', '223'])).
% 0.46/0.67  thf('225', plain,
% 0.46/0.67      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.67           sk_C)
% 0.46/0.67        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '224'])).
% 0.46/0.67  thf('226', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('227', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('228', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('229', plain,
% 0.46/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.67          sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['225', '226', '227', '228'])).
% 0.46/0.67  thf('230', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('231', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(reflexivity_r2_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.67         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.67       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.46/0.67  thf('232', plain,
% 0.46/0.67      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.67         ((r2_funct_2 @ X27 @ X28 @ X29 @ X29)
% 0.46/0.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.46/0.67          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.46/0.67          | ~ (v1_funct_1 @ X29)
% 0.46/0.67          | ~ (v1_funct_1 @ X30)
% 0.46/0.67          | ~ (v1_funct_2 @ X30 @ X27 @ X28)
% 0.46/0.67          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.46/0.67      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.46/0.67  thf('233', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.67             (k1_zfmisc_1 @ 
% 0.46/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.67          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.67          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.67             sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['231', '232'])).
% 0.46/0.67  thf('234', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('235', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('236', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.67             (k1_zfmisc_1 @ 
% 0.46/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.67          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.67             sk_C))),
% 0.46/0.67      inference('demod', [status(thm)], ['233', '234', '235'])).
% 0.46/0.67  thf('237', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['56', '57'])).
% 0.46/0.67  thf('238', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['56', '57'])).
% 0.46/0.67  thf('239', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('clc', [status(thm)], ['56', '57'])).
% 0.46/0.67  thf('240', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.67             (k1_zfmisc_1 @ 
% 0.46/0.67              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.67          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.67          | ~ (v1_funct_1 @ X0)
% 0.46/0.67          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.67             sk_C))),
% 0.46/0.67      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 0.46/0.67  thf('241', plain,
% 0.46/0.67      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['230', '240'])).
% 0.46/0.67  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('243', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.67  thf('244', plain,
% 0.46/0.67      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['241', '242', '243'])).
% 0.46/0.67  thf('245', plain, ($false), inference('demod', [status(thm)], ['229', '244'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
