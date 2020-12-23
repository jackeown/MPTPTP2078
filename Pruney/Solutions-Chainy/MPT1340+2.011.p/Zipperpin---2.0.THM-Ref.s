%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WWkJWOM4SG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:07 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  298 (8203 expanded)
%              Number of leaves         :   38 (2348 expanded)
%              Depth                    :   35
%              Number of atoms          : 2845 (178873 expanded)
%              Number of equality atoms :  140 (5149 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','9','10'])).

thf('12',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('31',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','39'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('52',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','49','50','51'])).

thf('53',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','39'])).

thf('66',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('73',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','75'])).

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

thf('77',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X25 @ X27 )
       != X25 )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_tops_2 @ X26 @ X25 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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
    inference('sup+',[status(thm)],['7','8'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79','92','93','107'])).

thf('109',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['52','109'])).

thf('111',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('113',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','75'])).

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

thf('116',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('120',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X25 @ X27 )
       != X25 )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_tops_2 @ X26 @ X25 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','75'])).

thf('127',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('131',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','75'])).

thf('136',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X20 ) @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('137',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('140',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('141',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','134','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('146',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('147',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','75'])).

thf('150',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('152',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t63_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) )).

thf('153',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) @ X30 )
       != ( k2_struct_0 @ X28 ) )
      | ~ ( v2_funct_1 @ X30 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['151','155'])).

thf('157',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','159'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('162',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('163',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('164',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['160','161','162','163','164'])).

thf('166',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','165'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('169',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('170',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('174',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X25 @ X27 )
       != X25 )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_tops_2 @ X26 @ X25 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('176',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('179',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('181',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('182',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('184',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','184'])).

thf('186',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','185'])).

thf('187',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('188',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('193',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['166','167','170','190','191','192'])).

thf('194',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','194'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('198',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('199',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['193'])).

thf('200',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('202',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('204',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != X14 )
      | ( v1_partfun1 @ X15 @ X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('205',plain,(
    ! [X15: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v4_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
      | ( v1_partfun1 @ X15 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['203','205'])).

thf('207',plain,(
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
    inference('sup-',[status(thm)],['202','206'])).

thf('208',plain,(
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
    inference('sup-',[status(thm)],['201','207'])).

thf('209',plain,(
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
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['200','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['199','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('214',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('217',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('218',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('220',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('221',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('223',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['212','213','214','215','218','221','222'])).

thf('224',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['198','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['197','228'])).

thf('230',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('231',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('232',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['193'])).

thf('233',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['229','230','231','232'])).

thf('234',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('235',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('237',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['196','237'])).

thf('239',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('240',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('241',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['238','239','240','241','242'])).

thf('244',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','243'])).

thf('245',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['114','245'])).

thf('247',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','246'])).

thf('248',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

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

thf('249',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_funct_2 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('250',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_funct_2 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['248','250'])).

thf('252',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('256',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    $false ),
    inference(demod,[status(thm)],['247','254','255','256','257'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WWkJWOM4SG
% 0.09/0.30  % Computer   : n013.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % DateTime   : Tue Dec  1 12:05:55 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.30  % Running portfolio for 600 s
% 0.09/0.30  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.09/0.30  % Number of cores: 8
% 0.09/0.30  % Python version: Python 3.6.8
% 0.09/0.31  % Running in FO mode
% 0.16/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.16/0.57  % Solved by: fo/fo7.sh
% 0.16/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.16/0.57  % done 380 iterations in 0.181s
% 0.16/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.16/0.57  % SZS output start Refutation
% 0.16/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.16/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.16/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.16/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.16/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.16/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.16/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.16/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.16/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.16/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.16/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.16/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.16/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.16/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.16/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.16/0.57  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.16/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.16/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.16/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.16/0.57  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.16/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.16/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.16/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.16/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.16/0.57  thf(t65_funct_1, axiom,
% 0.16/0.57    (![A:$i]:
% 0.16/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.16/0.57       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.16/0.57  thf('0', plain,
% 0.16/0.57      (![X1 : $i]:
% 0.16/0.57         (~ (v2_funct_1 @ X1)
% 0.16/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.16/0.57          | ~ (v1_funct_1 @ X1)
% 0.16/0.57          | ~ (v1_relat_1 @ X1))),
% 0.16/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.16/0.57  thf(d3_struct_0, axiom,
% 0.16/0.57    (![A:$i]:
% 0.16/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.16/0.57  thf('1', plain,
% 0.16/0.57      (![X23 : $i]:
% 0.16/0.57         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.57  thf('2', plain,
% 0.16/0.57      (![X23 : $i]:
% 0.16/0.57         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.57  thf(t64_tops_2, conjecture,
% 0.16/0.57    (![A:$i]:
% 0.16/0.57     ( ( l1_struct_0 @ A ) =>
% 0.16/0.57       ( ![B:$i]:
% 0.16/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.16/0.57           ( ![C:$i]:
% 0.16/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.16/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.16/0.57                 ( m1_subset_1 @
% 0.16/0.57                   C @ 
% 0.16/0.57                   ( k1_zfmisc_1 @
% 0.16/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.16/0.57               ( ( ( ( k2_relset_1 @
% 0.16/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.16/0.57                     ( k2_struct_0 @ B ) ) & 
% 0.16/0.57                   ( v2_funct_1 @ C ) ) =>
% 0.16/0.57                 ( r2_funct_2 @
% 0.16/0.57                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.16/0.57                   ( k2_tops_2 @
% 0.16/0.57                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.16/0.57                     ( k2_tops_2 @
% 0.16/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.16/0.57                   C ) ) ) ) ) ) ))).
% 0.16/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.16/0.57    (~( ![A:$i]:
% 0.16/0.57        ( ( l1_struct_0 @ A ) =>
% 0.16/0.57          ( ![B:$i]:
% 0.16/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.16/0.57              ( ![C:$i]:
% 0.16/0.57                ( ( ( v1_funct_1 @ C ) & 
% 0.16/0.57                    ( v1_funct_2 @
% 0.16/0.57                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.16/0.57                    ( m1_subset_1 @
% 0.16/0.57                      C @ 
% 0.16/0.57                      ( k1_zfmisc_1 @
% 0.16/0.57                        ( k2_zfmisc_1 @
% 0.16/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.16/0.57                  ( ( ( ( k2_relset_1 @
% 0.16/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.16/0.57                        ( k2_struct_0 @ B ) ) & 
% 0.16/0.57                      ( v2_funct_1 @ C ) ) =>
% 0.16/0.57                    ( r2_funct_2 @
% 0.16/0.57                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.16/0.57                      ( k2_tops_2 @
% 0.16/0.57                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.16/0.57                        ( k2_tops_2 @
% 0.16/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.16/0.57                      C ) ) ) ) ) ) ) )),
% 0.16/0.57    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.16/0.57  thf('3', plain,
% 0.16/0.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.16/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.16/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.16/0.57          sk_C)),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('4', plain,
% 0.16/0.57      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.16/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.16/0.57            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.16/0.57           sk_C)
% 0.16/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.16/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.16/0.57  thf('5', plain,
% 0.16/0.57      ((m1_subset_1 @ sk_C @ 
% 0.16/0.57        (k1_zfmisc_1 @ 
% 0.16/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.16/0.57    (![A:$i,B:$i,C:$i]:
% 0.16/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.16/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.16/0.57  thf('6', plain,
% 0.16/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.16/0.57         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.16/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.16/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.16/0.57  thf('7', plain,
% 0.16/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.57         = (k2_relat_1 @ sk_C))),
% 0.16/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.16/0.57  thf('8', plain,
% 0.16/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.57         = (k2_struct_0 @ sk_B))),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('9', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.57  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('11', plain,
% 0.16/0.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.16/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.16/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.16/0.57          sk_C)),
% 0.16/0.57      inference('demod', [status(thm)], ['4', '9', '10'])).
% 0.16/0.57  thf('12', plain,
% 0.16/0.57      (![X23 : $i]:
% 0.16/0.57         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.57  thf('13', plain,
% 0.16/0.57      ((m1_subset_1 @ sk_C @ 
% 0.16/0.57        (k1_zfmisc_1 @ 
% 0.16/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('14', plain,
% 0.16/0.57      (((m1_subset_1 @ sk_C @ 
% 0.16/0.57         (k1_zfmisc_1 @ 
% 0.16/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.16/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.16/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.16/0.57  thf('15', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('16', plain,
% 0.16/0.57      ((m1_subset_1 @ sk_C @ 
% 0.16/0.57        (k1_zfmisc_1 @ 
% 0.16/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.16/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.16/0.57  thf('17', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.57  thf('18', plain,
% 0.16/0.57      ((m1_subset_1 @ sk_C @ 
% 0.16/0.57        (k1_zfmisc_1 @ 
% 0.16/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.16/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.16/0.57  thf(cc5_funct_2, axiom,
% 0.16/0.57    (![A:$i,B:$i]:
% 0.16/0.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.16/0.57       ( ![C:$i]:
% 0.16/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.16/0.57           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.16/0.57             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.16/0.57  thf('19', plain,
% 0.16/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.16/0.57         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.16/0.57          | (v1_partfun1 @ X11 @ X12)
% 0.16/0.57          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.16/0.57          | ~ (v1_funct_1 @ X11)
% 0.16/0.57          | (v1_xboole_0 @ X13))),
% 0.16/0.57      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.16/0.57  thf('20', plain,
% 0.16/0.57      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.16/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.16/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.16/0.57        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.16/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.16/0.57  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('22', plain,
% 0.16/0.57      (![X23 : $i]:
% 0.16/0.57         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.57  thf('23', plain,
% 0.16/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('24', plain,
% 0.16/0.57      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.16/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.16/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.16/0.57  thf('25', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('26', plain,
% 0.16/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.16/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.16/0.57  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.57  thf('28', plain,
% 0.16/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.16/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.16/0.57  thf('29', plain,
% 0.16/0.57      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.16/0.57        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.16/0.57      inference('demod', [status(thm)], ['20', '21', '28'])).
% 0.16/0.57  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.57  thf('31', plain,
% 0.16/0.57      (![X23 : $i]:
% 0.16/0.57         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.57  thf(fc2_struct_0, axiom,
% 0.16/0.57    (![A:$i]:
% 0.16/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.16/0.57       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.16/0.57  thf('32', plain,
% 0.16/0.57      (![X24 : $i]:
% 0.16/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.16/0.57          | ~ (l1_struct_0 @ X24)
% 0.16/0.57          | (v2_struct_0 @ X24))),
% 0.16/0.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.16/0.57  thf('33', plain,
% 0.16/0.57      (![X0 : $i]:
% 0.16/0.57         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.16/0.57          | ~ (l1_struct_0 @ X0)
% 0.16/0.57          | (v2_struct_0 @ X0)
% 0.16/0.57          | ~ (l1_struct_0 @ X0))),
% 0.16/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.16/0.57  thf('34', plain,
% 0.16/0.57      (![X0 : $i]:
% 0.16/0.57         ((v2_struct_0 @ X0)
% 0.16/0.57          | ~ (l1_struct_0 @ X0)
% 0.16/0.57          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.16/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.16/0.57  thf('35', plain,
% 0.16/0.57      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.16/0.57        | ~ (l1_struct_0 @ sk_B)
% 0.16/0.57        | (v2_struct_0 @ sk_B))),
% 0.16/0.57      inference('sup-', [status(thm)], ['30', '34'])).
% 0.16/0.57  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('37', plain,
% 0.16/0.57      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.16/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.16/0.57  thf('38', plain, (~ (v2_struct_0 @ sk_B)),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf('39', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.16/0.57      inference('clc', [status(thm)], ['37', '38'])).
% 0.16/0.57  thf('40', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.16/0.57      inference('clc', [status(thm)], ['29', '39'])).
% 0.16/0.57  thf(d4_partfun1, axiom,
% 0.16/0.57    (![A:$i,B:$i]:
% 0.16/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.16/0.57       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.16/0.57  thf('41', plain,
% 0.16/0.57      (![X14 : $i, X15 : $i]:
% 0.16/0.57         (~ (v1_partfun1 @ X15 @ X14)
% 0.16/0.57          | ((k1_relat_1 @ X15) = (X14))
% 0.16/0.57          | ~ (v4_relat_1 @ X15 @ X14)
% 0.16/0.57          | ~ (v1_relat_1 @ X15))),
% 0.16/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.16/0.57  thf('42', plain,
% 0.16/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.16/0.57        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.16/0.57        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.16/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.16/0.57  thf('43', plain,
% 0.16/0.57      ((m1_subset_1 @ sk_C @ 
% 0.16/0.57        (k1_zfmisc_1 @ 
% 0.16/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf(cc1_relset_1, axiom,
% 0.16/0.57    (![A:$i,B:$i,C:$i]:
% 0.16/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.16/0.57       ( v1_relat_1 @ C ) ))).
% 0.16/0.57  thf('44', plain,
% 0.16/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.16/0.57         ((v1_relat_1 @ X2)
% 0.16/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.16/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.16/0.57  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.16/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.16/0.57  thf('46', plain,
% 0.16/0.57      ((m1_subset_1 @ sk_C @ 
% 0.16/0.57        (k1_zfmisc_1 @ 
% 0.16/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.57  thf(cc2_relset_1, axiom,
% 0.16/0.57    (![A:$i,B:$i,C:$i]:
% 0.16/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.16/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.16/0.57  thf('47', plain,
% 0.16/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.16/0.57         ((v4_relat_1 @ X5 @ X6)
% 0.16/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.16/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.16/0.57  thf('48', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.16/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.16/0.57  thf('49', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.16/0.57      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.16/0.57  thf('50', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.16/0.57      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.16/0.57  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.16/0.57      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.16/0.57  thf('52', plain,
% 0.16/0.57      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.16/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.57           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.16/0.57          sk_C)),
% 0.16/0.57      inference('demod', [status(thm)], ['11', '49', '50', '51'])).
% 0.16/0.58  thf('53', plain,
% 0.16/0.58      (![X23 : $i]:
% 0.16/0.58         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.58  thf('54', plain,
% 0.16/0.58      (![X23 : $i]:
% 0.16/0.58         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.58  thf('55', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('56', plain,
% 0.16/0.58      (((m1_subset_1 @ sk_C @ 
% 0.16/0.58         (k1_zfmisc_1 @ 
% 0.16/0.58          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.16/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.16/0.58      inference('sup+', [status(thm)], ['54', '55'])).
% 0.16/0.58  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('58', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.16/0.58  thf('59', plain,
% 0.16/0.58      (((m1_subset_1 @ sk_C @ 
% 0.16/0.58         (k1_zfmisc_1 @ 
% 0.16/0.58          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.16/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['53', '58'])).
% 0.16/0.58  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('61', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.16/0.58      inference('demod', [status(thm)], ['59', '60'])).
% 0.16/0.58  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.58  thf('63', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.16/0.58      inference('demod', [status(thm)], ['61', '62'])).
% 0.16/0.58  thf('64', plain,
% 0.16/0.58      (![X23 : $i]:
% 0.16/0.58         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.58  thf('65', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.16/0.58      inference('clc', [status(thm)], ['29', '39'])).
% 0.16/0.58  thf('66', plain,
% 0.16/0.58      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.16/0.58      inference('sup+', [status(thm)], ['64', '65'])).
% 0.16/0.58  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('68', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['66', '67'])).
% 0.16/0.58  thf('69', plain,
% 0.16/0.58      (![X14 : $i, X15 : $i]:
% 0.16/0.58         (~ (v1_partfun1 @ X15 @ X14)
% 0.16/0.58          | ((k1_relat_1 @ X15) = (X14))
% 0.16/0.58          | ~ (v4_relat_1 @ X15 @ X14)
% 0.16/0.58          | ~ (v1_relat_1 @ X15))),
% 0.16/0.58      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.16/0.58  thf('70', plain,
% 0.16/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.16/0.58        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.16/0.58        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.16/0.58  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.16/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.16/0.58  thf('72', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.16/0.58  thf('73', plain,
% 0.16/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.16/0.58         ((v4_relat_1 @ X5 @ X6)
% 0.16/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.16/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.16/0.58  thf('74', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.16/0.58  thf('75', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.16/0.58  thf('76', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.16/0.58      inference('demod', [status(thm)], ['63', '75'])).
% 0.16/0.58  thf(d4_tops_2, axiom,
% 0.16/0.58    (![A:$i,B:$i,C:$i]:
% 0.16/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.16/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.16/0.58       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.16/0.58         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.16/0.58  thf('77', plain,
% 0.16/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.16/0.58         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.16/0.58          | ~ (v2_funct_1 @ X27)
% 0.16/0.58          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.16/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.16/0.58          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.16/0.58          | ~ (v1_funct_1 @ X27))),
% 0.16/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.16/0.58  thf('78', plain,
% 0.16/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.16/0.58        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58            = (k2_funct_1 @ sk_C))
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.16/0.58        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58            != (k2_relat_1 @ sk_C)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.16/0.58  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('80', plain,
% 0.16/0.58      (![X23 : $i]:
% 0.16/0.58         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.58  thf('81', plain,
% 0.16/0.58      (![X23 : $i]:
% 0.16/0.58         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.58  thf('82', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('83', plain,
% 0.16/0.58      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.16/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.16/0.58      inference('sup+', [status(thm)], ['81', '82'])).
% 0.16/0.58  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('85', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.16/0.58      inference('demod', [status(thm)], ['83', '84'])).
% 0.16/0.58  thf('86', plain,
% 0.16/0.58      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.16/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['80', '85'])).
% 0.16/0.58  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('88', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('demod', [status(thm)], ['86', '87'])).
% 0.16/0.58  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.58  thf('90', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['88', '89'])).
% 0.16/0.58  thf('91', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.16/0.58  thf('92', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['90', '91'])).
% 0.16/0.58  thf('93', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('94', plain,
% 0.16/0.58      (![X23 : $i]:
% 0.16/0.58         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.58  thf('95', plain,
% 0.16/0.58      (![X23 : $i]:
% 0.16/0.58         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.58  thf('96', plain,
% 0.16/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58         = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('97', plain,
% 0.16/0.58      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58          = (k2_struct_0 @ sk_B))
% 0.16/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.16/0.58      inference('sup+', [status(thm)], ['95', '96'])).
% 0.16/0.58  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('99', plain,
% 0.16/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58         = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('demod', [status(thm)], ['97', '98'])).
% 0.16/0.58  thf('100', plain,
% 0.16/0.58      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58          = (k2_struct_0 @ sk_B))
% 0.16/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['94', '99'])).
% 0.16/0.58  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('102', plain,
% 0.16/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58         = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('demod', [status(thm)], ['100', '101'])).
% 0.16/0.58  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.58  thf('104', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.58  thf('105', plain,
% 0.16/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58         = (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.16/0.58  thf('106', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.16/0.58  thf('107', plain,
% 0.16/0.58      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58         = (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['105', '106'])).
% 0.16/0.58  thf('108', plain,
% 0.16/0.58      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58          = (k2_funct_1 @ sk_C))
% 0.16/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['78', '79', '92', '93', '107'])).
% 0.16/0.58  thf('109', plain,
% 0.16/0.58      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58         = (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('simplify', [status(thm)], ['108'])).
% 0.16/0.58  thf('110', plain,
% 0.16/0.58      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.16/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58           (k2_funct_1 @ sk_C)) @ 
% 0.16/0.58          sk_C)),
% 0.16/0.58      inference('demod', [status(thm)], ['52', '109'])).
% 0.16/0.58  thf('111', plain,
% 0.16/0.58      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.16/0.58           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58            (k2_funct_1 @ sk_C)) @ 
% 0.16/0.58           sk_C)
% 0.16/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup-', [status(thm)], ['1', '110'])).
% 0.16/0.58  thf('112', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.58  thf('113', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('114', plain,
% 0.16/0.58      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.16/0.58          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58           (k2_funct_1 @ sk_C)) @ 
% 0.16/0.58          sk_C)),
% 0.16/0.58      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.16/0.58  thf('115', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.16/0.58      inference('demod', [status(thm)], ['63', '75'])).
% 0.16/0.58  thf(t31_funct_2, axiom,
% 0.16/0.58    (![A:$i,B:$i,C:$i]:
% 0.16/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.16/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.16/0.58       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.16/0.58         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.16/0.58           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.16/0.58           ( m1_subset_1 @
% 0.16/0.58             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.16/0.58  thf('116', plain,
% 0.16/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X20)
% 0.16/0.58          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.16/0.58          | (m1_subset_1 @ (k2_funct_1 @ X20) @ 
% 0.16/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.16/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.16/0.58          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.16/0.58          | ~ (v1_funct_1 @ X20))),
% 0.16/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.16/0.58  thf('117', plain,
% 0.16/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.16/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.16/0.58           (k1_zfmisc_1 @ 
% 0.16/0.58            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.16/0.58        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58            != (k2_relat_1 @ sk_C))
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.16/0.58      inference('sup-', [status(thm)], ['115', '116'])).
% 0.16/0.58  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('119', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['90', '91'])).
% 0.16/0.58  thf('120', plain,
% 0.16/0.58      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58         = (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['105', '106'])).
% 0.16/0.58  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('122', plain,
% 0.16/0.58      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.16/0.58         (k1_zfmisc_1 @ 
% 0.16/0.58          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.16/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 0.16/0.58  thf('123', plain,
% 0.16/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.16/0.58      inference('simplify', [status(thm)], ['122'])).
% 0.16/0.58  thf('124', plain,
% 0.16/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.16/0.58         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.16/0.58          | ~ (v2_funct_1 @ X27)
% 0.16/0.58          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.16/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.16/0.58          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.16/0.58          | ~ (v1_funct_1 @ X27))),
% 0.16/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.16/0.58  thf('125', plain,
% 0.16/0.58      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.16/0.58             (k1_relat_1 @ sk_C))
% 0.16/0.58        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.16/0.58        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['123', '124'])).
% 0.16/0.58  thf('126', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.16/0.58      inference('demod', [status(thm)], ['63', '75'])).
% 0.16/0.58  thf('127', plain,
% 0.16/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X20)
% 0.16/0.58          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.16/0.58          | (v1_funct_1 @ (k2_funct_1 @ X20))
% 0.16/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.16/0.58          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.16/0.58          | ~ (v1_funct_1 @ X20))),
% 0.16/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.16/0.58  thf('128', plain,
% 0.16/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.16/0.58        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58            != (k2_relat_1 @ sk_C))
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.16/0.58      inference('sup-', [status(thm)], ['126', '127'])).
% 0.16/0.58  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('130', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['90', '91'])).
% 0.16/0.58  thf('131', plain,
% 0.16/0.58      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58         = (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['105', '106'])).
% 0.16/0.58  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('133', plain,
% 0.16/0.58      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 0.16/0.58  thf('134', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('simplify', [status(thm)], ['133'])).
% 0.16/0.58  thf('135', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.16/0.58      inference('demod', [status(thm)], ['63', '75'])).
% 0.16/0.58  thf('136', plain,
% 0.16/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X20)
% 0.16/0.58          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.16/0.58          | (v1_funct_2 @ (k2_funct_1 @ X20) @ X21 @ X22)
% 0.16/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.16/0.58          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.16/0.58          | ~ (v1_funct_1 @ X20))),
% 0.16/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.16/0.58  thf('137', plain,
% 0.16/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.16/0.58        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.16/0.58           (k1_relat_1 @ sk_C))
% 0.16/0.58        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58            != (k2_relat_1 @ sk_C))
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.16/0.58      inference('sup-', [status(thm)], ['135', '136'])).
% 0.16/0.58  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('139', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['90', '91'])).
% 0.16/0.58  thf('140', plain,
% 0.16/0.58      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.16/0.58         = (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['105', '106'])).
% 0.16/0.58  thf('141', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('142', plain,
% 0.16/0.58      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.16/0.58         (k1_relat_1 @ sk_C))
% 0.16/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 0.16/0.58  thf('143', plain,
% 0.16/0.58      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.16/0.58        (k1_relat_1 @ sk_C))),
% 0.16/0.58      inference('simplify', [status(thm)], ['142'])).
% 0.16/0.58  thf('144', plain,
% 0.16/0.58      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.16/0.58        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['125', '134', '143'])).
% 0.16/0.58  thf('145', plain,
% 0.16/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.16/0.58      inference('simplify', [status(thm)], ['122'])).
% 0.16/0.58  thf('146', plain,
% 0.16/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.16/0.58         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.16/0.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.16/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.16/0.58  thf('147', plain,
% 0.16/0.58      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['145', '146'])).
% 0.16/0.58  thf('148', plain,
% 0.16/0.58      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.16/0.58        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['144', '147'])).
% 0.16/0.58  thf('149', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.16/0.58      inference('demod', [status(thm)], ['63', '75'])).
% 0.16/0.58  thf('150', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.16/0.58  thf('151', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.58  thf('152', plain,
% 0.16/0.58      (![X23 : $i]:
% 0.16/0.58         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.58  thf(t63_tops_2, axiom,
% 0.16/0.58    (![A:$i]:
% 0.16/0.58     ( ( l1_struct_0 @ A ) =>
% 0.16/0.58       ( ![B:$i]:
% 0.16/0.58         ( ( l1_struct_0 @ B ) =>
% 0.16/0.58           ( ![C:$i]:
% 0.16/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.16/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.16/0.58                 ( m1_subset_1 @
% 0.16/0.58                   C @ 
% 0.16/0.58                   ( k1_zfmisc_1 @
% 0.16/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.16/0.58               ( ( ( ( k2_relset_1 @
% 0.16/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.16/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.16/0.58                   ( v2_funct_1 @ C ) ) =>
% 0.16/0.58                 ( v2_funct_1 @
% 0.16/0.58                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.16/0.58  thf('153', plain,
% 0.16/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.16/0.58         (~ (l1_struct_0 @ X28)
% 0.16/0.58          | ((k2_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28) @ X30)
% 0.16/0.58              != (k2_struct_0 @ X28))
% 0.16/0.58          | ~ (v2_funct_1 @ X30)
% 0.16/0.58          | (v2_funct_1 @ 
% 0.16/0.58             (k2_tops_2 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28) @ X30))
% 0.16/0.58          | ~ (m1_subset_1 @ X30 @ 
% 0.16/0.58               (k1_zfmisc_1 @ 
% 0.16/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.16/0.58          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.16/0.58          | ~ (v1_funct_1 @ X30)
% 0.16/0.58          | ~ (l1_struct_0 @ X29))),
% 0.16/0.58      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.16/0.58  thf('154', plain,
% 0.16/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.58         (~ (m1_subset_1 @ X2 @ 
% 0.16/0.58             (k1_zfmisc_1 @ 
% 0.16/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.16/0.58          | ~ (l1_struct_0 @ X0)
% 0.16/0.58          | ~ (l1_struct_0 @ X1)
% 0.16/0.58          | ~ (v1_funct_1 @ X2)
% 0.16/0.58          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.16/0.58          | (v2_funct_1 @ 
% 0.16/0.58             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.16/0.58          | ~ (v2_funct_1 @ X2)
% 0.16/0.58          | ((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.16/0.58              != (k2_struct_0 @ X0))
% 0.16/0.58          | ~ (l1_struct_0 @ X0))),
% 0.16/0.58      inference('sup-', [status(thm)], ['152', '153'])).
% 0.16/0.58  thf('155', plain,
% 0.16/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.58         (((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.16/0.58            != (k2_struct_0 @ X0))
% 0.16/0.58          | ~ (v2_funct_1 @ X2)
% 0.16/0.58          | (v2_funct_1 @ 
% 0.16/0.58             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.16/0.58          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.16/0.58          | ~ (v1_funct_1 @ X2)
% 0.16/0.58          | ~ (l1_struct_0 @ X1)
% 0.16/0.58          | ~ (l1_struct_0 @ X0)
% 0.16/0.58          | ~ (m1_subset_1 @ X2 @ 
% 0.16/0.58               (k1_zfmisc_1 @ 
% 0.16/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))))),
% 0.16/0.58      inference('simplify', [status(thm)], ['154'])).
% 0.16/0.58  thf('156', plain,
% 0.16/0.58      (![X0 : $i, X1 : $i]:
% 0.16/0.58         (~ (m1_subset_1 @ X1 @ 
% 0.16/0.58             (k1_zfmisc_1 @ 
% 0.16/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.16/0.58          | ~ (l1_struct_0 @ sk_B)
% 0.16/0.58          | ~ (l1_struct_0 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X1)
% 0.16/0.58          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.16/0.58          | (v2_funct_1 @ 
% 0.16/0.58             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.16/0.58          | ~ (v2_funct_1 @ X1)
% 0.16/0.58          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.16/0.58              != (k2_struct_0 @ sk_B)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['151', '155'])).
% 0.16/0.58  thf('157', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('158', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.58  thf('159', plain,
% 0.16/0.58      (![X0 : $i, X1 : $i]:
% 0.16/0.58         (~ (m1_subset_1 @ X1 @ 
% 0.16/0.58             (k1_zfmisc_1 @ 
% 0.16/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.16/0.58          | ~ (l1_struct_0 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X1)
% 0.16/0.58          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.16/0.58          | (v2_funct_1 @ 
% 0.16/0.58             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.16/0.58          | ~ (v2_funct_1 @ X1)
% 0.16/0.58          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.16/0.58              != (k2_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['156', '157', '158'])).
% 0.16/0.58  thf('160', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (m1_subset_1 @ X0 @ 
% 0.16/0.58             (k1_zfmisc_1 @ 
% 0.16/0.58              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.16/0.58          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0)
% 0.16/0.58              != (k2_relat_1 @ sk_C))
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | (v2_funct_1 @ 
% 0.16/0.58             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0))
% 0.16/0.58          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (l1_struct_0 @ sk_A))),
% 0.16/0.58      inference('sup-', [status(thm)], ['150', '159'])).
% 0.16/0.58  thf('161', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.16/0.58  thf('162', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.16/0.58  thf('163', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.16/0.58  thf('164', plain, ((l1_struct_0 @ sk_A)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('165', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (m1_subset_1 @ X0 @ 
% 0.16/0.58             (k1_zfmisc_1 @ 
% 0.16/0.58              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.16/0.58          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0)
% 0.16/0.58              != (k2_relat_1 @ sk_C))
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | (v2_funct_1 @ 
% 0.16/0.58             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0))
% 0.16/0.58          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.16/0.58          | ~ (v1_funct_1 @ X0))),
% 0.16/0.58      inference('demod', [status(thm)], ['160', '161', '162', '163', '164'])).
% 0.16/0.58  thf('166', plain,
% 0.16/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.16/0.58        | (v2_funct_1 @ 
% 0.16/0.58           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.16/0.58        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58            != (k2_relat_1 @ sk_C)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['149', '165'])).
% 0.16/0.58  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('168', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.16/0.58      inference('demod', [status(thm)], ['83', '84'])).
% 0.16/0.58  thf('169', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.16/0.58  thf('170', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.16/0.58      inference('demod', [status(thm)], ['168', '169'])).
% 0.16/0.58  thf('171', plain,
% 0.16/0.58      (![X23 : $i]:
% 0.16/0.58         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.16/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.16/0.58  thf('172', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.16/0.58  thf('173', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.16/0.58  thf('174', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.58      inference('demod', [status(thm)], ['172', '173'])).
% 0.16/0.58  thf('175', plain,
% 0.16/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.16/0.58         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.16/0.58          | ~ (v2_funct_1 @ X27)
% 0.16/0.58          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.16/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.16/0.58          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.16/0.58          | ~ (v1_funct_1 @ X27))),
% 0.16/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.16/0.58  thf('176', plain,
% 0.16/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.16/0.58        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58            = (k2_funct_1 @ sk_C))
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.16/0.58        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58            != (u1_struct_0 @ sk_B)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['174', '175'])).
% 0.16/0.58  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('178', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.16/0.58      inference('demod', [status(thm)], ['168', '169'])).
% 0.16/0.58  thf('179', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('180', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.16/0.58  thf('181', plain,
% 0.16/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.16/0.58         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.16/0.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.16/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.16/0.58  thf('182', plain,
% 0.16/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58         = (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('sup-', [status(thm)], ['180', '181'])).
% 0.16/0.58  thf('183', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.16/0.58  thf('184', plain,
% 0.16/0.58      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58         = (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['182', '183'])).
% 0.16/0.58  thf('185', plain,
% 0.16/0.58      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58          = (k2_funct_1 @ sk_C))
% 0.16/0.58        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.16/0.58      inference('demod', [status(thm)], ['176', '177', '178', '179', '184'])).
% 0.16/0.58  thf('186', plain,
% 0.16/0.58      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.16/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.16/0.58        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58            = (k2_funct_1 @ sk_C)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['171', '185'])).
% 0.16/0.58  thf('187', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.16/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.16/0.58  thf('188', plain, ((l1_struct_0 @ sk_B)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('189', plain,
% 0.16/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.16/0.58        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58            = (k2_funct_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.16/0.58  thf('190', plain,
% 0.16/0.58      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58         = (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('simplify', [status(thm)], ['189'])).
% 0.16/0.58  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('192', plain,
% 0.16/0.58      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.16/0.58         = (k2_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['182', '183'])).
% 0.16/0.58  thf('193', plain,
% 0.16/0.58      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)],
% 0.16/0.58                ['166', '167', '170', '190', '191', '192'])).
% 0.16/0.58  thf('194', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('simplify', [status(thm)], ['193'])).
% 0.16/0.58  thf('195', plain,
% 0.16/0.58      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.16/0.58        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['148', '194'])).
% 0.16/0.58  thf(t55_funct_1, axiom,
% 0.16/0.58    (![A:$i]:
% 0.16/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.16/0.58       ( ( v2_funct_1 @ A ) =>
% 0.16/0.58         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.16/0.58           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.16/0.58  thf('196', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X0)
% 0.16/0.58          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ X0))),
% 0.16/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.16/0.58  thf('197', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X0)
% 0.16/0.58          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ X0))),
% 0.16/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.16/0.58  thf('198', plain,
% 0.16/0.58      (![X1 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X1)
% 0.16/0.58          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.16/0.58          | ~ (v1_funct_1 @ X1)
% 0.16/0.58          | ~ (v1_relat_1 @ X1))),
% 0.16/0.58      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.16/0.58  thf('199', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('simplify', [status(thm)], ['193'])).
% 0.16/0.58  thf('200', plain,
% 0.16/0.58      (![X1 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X1)
% 0.16/0.58          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.16/0.58          | ~ (v1_funct_1 @ X1)
% 0.16/0.58          | ~ (v1_relat_1 @ X1))),
% 0.16/0.58      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.16/0.58  thf('201', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X0)
% 0.16/0.58          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ X0))),
% 0.16/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.16/0.58  thf('202', plain,
% 0.16/0.58      (![X1 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X1)
% 0.16/0.58          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.16/0.58          | ~ (v1_funct_1 @ X1)
% 0.16/0.58          | ~ (v1_relat_1 @ X1))),
% 0.16/0.58      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.16/0.58  thf('203', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (v2_funct_1 @ X0)
% 0.16/0.58          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ X0))),
% 0.16/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.16/0.58  thf('204', plain,
% 0.16/0.58      (![X14 : $i, X15 : $i]:
% 0.16/0.58         (((k1_relat_1 @ X15) != (X14))
% 0.16/0.58          | (v1_partfun1 @ X15 @ X14)
% 0.16/0.58          | ~ (v4_relat_1 @ X15 @ X14)
% 0.16/0.58          | ~ (v1_relat_1 @ X15))),
% 0.16/0.58      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.16/0.58  thf('205', plain,
% 0.16/0.58      (![X15 : $i]:
% 0.16/0.58         (~ (v1_relat_1 @ X15)
% 0.16/0.58          | ~ (v4_relat_1 @ X15 @ (k1_relat_1 @ X15))
% 0.16/0.58          | (v1_partfun1 @ X15 @ (k1_relat_1 @ X15)))),
% 0.16/0.58      inference('simplify', [status(thm)], ['204'])).
% 0.16/0.58  thf('206', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.16/0.58          | ~ (v1_relat_1 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.16/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['203', '205'])).
% 0.16/0.58  thf('207', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.16/0.58          | ~ (v1_relat_1 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.16/0.58          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.16/0.58             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.16/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.16/0.58      inference('sup-', [status(thm)], ['202', '206'])).
% 0.16/0.58  thf('208', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.16/0.58          | ~ (v1_relat_1 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.16/0.58             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.16/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ X0))),
% 0.16/0.58      inference('sup-', [status(thm)], ['201', '207'])).
% 0.16/0.58  thf('209', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.16/0.58          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.16/0.58             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.16/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ X0)
% 0.16/0.58          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.16/0.58      inference('simplify', [status(thm)], ['208'])).
% 0.16/0.58  thf('210', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         (~ (v1_relat_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.16/0.58          | ~ (v1_relat_1 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.16/0.58             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.16/0.58      inference('sup-', [status(thm)], ['200', '209'])).
% 0.16/0.58  thf('211', plain,
% 0.16/0.58      (![X0 : $i]:
% 0.16/0.58         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.16/0.58           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.16/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.16/0.58          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.16/0.58          | ~ (v2_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_funct_1 @ X0)
% 0.16/0.58          | ~ (v1_relat_1 @ X0))),
% 0.16/0.58      inference('simplify', [status(thm)], ['210'])).
% 0.16/0.58  thf('212', plain,
% 0.16/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.16/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.16/0.58           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.16/0.58      inference('sup-', [status(thm)], ['199', '211'])).
% 0.16/0.58  thf('213', plain, ((v1_relat_1 @ sk_C)),
% 0.16/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.16/0.58  thf('214', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('215', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('216', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.16/0.58  thf('217', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.16/0.58      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.16/0.58  thf('218', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['216', '217'])).
% 0.16/0.58  thf('219', plain,
% 0.16/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.16/0.58      inference('simplify', [status(thm)], ['122'])).
% 0.16/0.58  thf('220', plain,
% 0.16/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.16/0.58         ((v1_relat_1 @ X2)
% 0.16/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.16/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.16/0.58  thf('221', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('sup-', [status(thm)], ['219', '220'])).
% 0.16/0.58  thf('222', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('simplify', [status(thm)], ['133'])).
% 0.16/0.58  thf('223', plain,
% 0.16/0.58      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.16/0.58        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.16/0.58      inference('demod', [status(thm)],
% 0.16/0.58                ['212', '213', '214', '215', '218', '221', '222'])).
% 0.16/0.58  thf('224', plain,
% 0.16/0.58      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.16/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.16/0.58      inference('sup+', [status(thm)], ['198', '223'])).
% 0.16/0.58  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.16/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.16/0.58  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('228', plain,
% 0.16/0.58      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.16/0.58      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 0.16/0.58  thf('229', plain,
% 0.16/0.58      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.16/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.16/0.58        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.16/0.58      inference('sup+', [status(thm)], ['197', '228'])).
% 0.16/0.58  thf('230', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('sup-', [status(thm)], ['219', '220'])).
% 0.16/0.58  thf('231', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('simplify', [status(thm)], ['133'])).
% 0.16/0.58  thf('232', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.16/0.58      inference('simplify', [status(thm)], ['193'])).
% 0.16/0.58  thf('233', plain,
% 0.16/0.58      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['229', '230', '231', '232'])).
% 0.16/0.58  thf('234', plain,
% 0.16/0.58      (![X14 : $i, X15 : $i]:
% 0.16/0.58         (~ (v1_partfun1 @ X15 @ X14)
% 0.16/0.58          | ((k1_relat_1 @ X15) = (X14))
% 0.16/0.58          | ~ (v4_relat_1 @ X15 @ X14)
% 0.16/0.58          | ~ (v1_relat_1 @ X15))),
% 0.16/0.58      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.16/0.58  thf('235', plain,
% 0.16/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.16/0.58        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.16/0.58        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.16/0.58      inference('sup-', [status(thm)], ['233', '234'])).
% 0.16/0.58  thf('236', plain, ((v1_relat_1 @ sk_C)),
% 0.16/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.16/0.58  thf('237', plain,
% 0.16/0.58      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.16/0.58        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.16/0.58      inference('demod', [status(thm)], ['235', '236'])).
% 0.16/0.58  thf('238', plain,
% 0.16/0.58      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.16/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.16/0.58        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.16/0.58      inference('sup-', [status(thm)], ['196', '237'])).
% 0.16/0.58  thf('239', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.16/0.58      inference('demod', [status(thm)], ['216', '217'])).
% 0.16/0.58  thf('240', plain, ((v1_relat_1 @ sk_C)),
% 0.16/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.16/0.58  thf('241', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('242', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('243', plain,
% 0.16/0.58      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['238', '239', '240', '241', '242'])).
% 0.16/0.58  thf('244', plain,
% 0.16/0.58      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.16/0.58        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.16/0.58      inference('demod', [status(thm)], ['195', '243'])).
% 0.16/0.58  thf('245', plain,
% 0.16/0.58      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.16/0.58         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.16/0.58      inference('simplify', [status(thm)], ['244'])).
% 0.16/0.58  thf('246', plain,
% 0.16/0.58      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.16/0.58          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.16/0.58      inference('demod', [status(thm)], ['114', '245'])).
% 0.16/0.58  thf('247', plain,
% 0.16/0.58      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.16/0.58           sk_C)
% 0.16/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.16/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.16/0.58      inference('sup-', [status(thm)], ['0', '246'])).
% 0.16/0.58  thf('248', plain,
% 0.16/0.58      ((m1_subset_1 @ sk_C @ 
% 0.16/0.58        (k1_zfmisc_1 @ 
% 0.16/0.58         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.16/0.58      inference('demod', [status(thm)], ['172', '173'])).
% 0.16/0.58  thf(redefinition_r2_funct_2, axiom,
% 0.16/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.16/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.16/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.16/0.58         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.16/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.16/0.58       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.16/0.58  thf('249', plain,
% 0.16/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.16/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.16/0.58          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.16/0.58          | ~ (v1_funct_1 @ X16)
% 0.16/0.58          | ~ (v1_funct_1 @ X19)
% 0.16/0.58          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.16/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.16/0.58          | (r2_funct_2 @ X17 @ X18 @ X16 @ X19)
% 0.16/0.58          | ((X16) != (X19)))),
% 0.16/0.58      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.16/0.58  thf('250', plain,
% 0.16/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.16/0.58         ((r2_funct_2 @ X17 @ X18 @ X19 @ X19)
% 0.16/0.58          | ~ (v1_funct_1 @ X19)
% 0.16/0.58          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.16/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.16/0.58      inference('simplify', [status(thm)], ['249'])).
% 0.16/0.58  thf('251', plain,
% 0.16/0.58      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.16/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.16/0.58        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.16/0.58           sk_C))),
% 0.16/0.58      inference('sup-', [status(thm)], ['248', '250'])).
% 0.16/0.58  thf('252', plain,
% 0.16/0.58      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.16/0.58      inference('demod', [status(thm)], ['168', '169'])).
% 0.16/0.58  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('254', plain,
% 0.16/0.58      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.16/0.58      inference('demod', [status(thm)], ['251', '252', '253'])).
% 0.16/0.58  thf('255', plain, ((v1_relat_1 @ sk_C)),
% 0.16/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.16/0.58  thf('256', plain, ((v1_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('257', plain, ((v2_funct_1 @ sk_C)),
% 0.16/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.58  thf('258', plain, ($false),
% 0.16/0.58      inference('demod', [status(thm)], ['247', '254', '255', '256', '257'])).
% 0.16/0.58  
% 0.16/0.58  % SZS output end Refutation
% 0.16/0.58  
% 0.16/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
