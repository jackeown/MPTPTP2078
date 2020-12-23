%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W76x7jbubj

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:58 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  334 (40268 expanded)
%              Number of leaves         :   53 (11757 expanded)
%              Depth                    :   29
%              Number of atoms          : 2807 (931001 expanded)
%              Number of equality atoms :  180 (45858 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
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
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( v1_partfun1 @ X39 @ X40 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('19',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(condensation,[status(thm)],['28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X48: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','38'])).

thf('40',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','39'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('41',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_partfun1 @ X43 @ X42 )
      | ( ( k1_relat_1 @ X43 )
        = X42 )
      | ~ ( v4_relat_1 @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','51'])).

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

thf('53',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X46 @ X45 @ X44 )
       != X45 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','39'])).

thf('69',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_partfun1 @ X43 @ X42 )
      | ( ( k1_relat_1 @ X43 )
        = X42 )
      | ~ ( v4_relat_1 @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('75',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('81',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','81'])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('85',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('97',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','83','89','99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('104',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['104'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('106',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X17 ) @ ( k9_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['103','107'])).

thf('109',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('110',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('113',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('115',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['113','116'])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','81'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('122',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X27 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('123',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('125',plain,(
    v4_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('127',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k3_relset_1 @ X37 @ X38 @ X36 )
        = ( k4_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('128',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','128'])).

thf('130',plain,
    ( ( v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['120','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('132',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k4_relat_1 @ sk_C )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('137',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('138',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('140',plain,(
    v1_relat_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('142',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','142'])).

thf('144',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('145',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('147',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('151',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','119','147','148','149','150'])).

thf('152',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['102','151'])).

thf('153',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( v1_partfun1 @ X39 @ X40 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('154',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','51'])).

thf('156',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X46 @ X45 @ X44 )
       != X45 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','82'])).

thf('160',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('161',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('162',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','161','162'])).

thf('164',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','51'])).

thf('166',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X46 @ X45 @ X44 )
       != X45 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X44 ) @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('167',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','82'])).

thf('170',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('171',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171','172'])).

thf('174',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','119','147','148','149','150'])).

thf('176',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','164','176'])).

thf('178',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_partfun1 @ X43 @ X42 )
      | ( ( k1_relat_1 @ X43 )
        = X42 )
      | ~ ( v4_relat_1 @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('179',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('181',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('182',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('184',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['184'])).

thf('186',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['183','185'])).

thf('187',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('190',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','119','147','148','149','150'])).

thf('191',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('193',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','51'])).

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

thf('195',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k2_relset_1 @ X50 @ X49 @ X51 )
       != X49 )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_tops_2 @ X50 @ X49 @ X51 )
        = ( k2_funct_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('196',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','82'])).

thf('199',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('202',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['196','197','198','199','200','201'])).

thf('203',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','119','147','148','149','150'])).

thf('205',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('207',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('208',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('210',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('211',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('212',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('214',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['188','191','192','193','205','212','213'])).

thf('215',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('216',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('217',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','81'])).

thf('219',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('220',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('221',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['184'])).

thf('222',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('226',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['218','227'])).

thf('229',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('230',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','81'])).

thf('231',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('233',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','119','147','148','149','150'])).

thf('234',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('235',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','119','147','148','149','150'])).

thf('236',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['231','232','233','234','235'])).

thf('237',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['217','236'])).

thf('238',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['184'])).

thf('240',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['238','239'])).

thf('241',plain,(
    ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['214','240'])).

thf('242',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['182','241'])).

thf('243',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['182','241'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('245',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['242','245'])).

thf('247',plain,(
    ! [X47: $i] :
      ( ( ( k2_struct_0 @ X47 )
        = ( u1_struct_0 @ X47 ) )
      | ~ ( l1_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('249',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['250','251'])).

thf('253',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['247','252'])).

thf('254',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','81'])).

thf('257',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','119','147','148','149','150'])).

thf('259',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['182','241'])).

thf('261',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('265',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['243','244'])).

thf('269',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('270',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('271',plain,
    ( ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['182','241'])).

thf('273',plain,(
    v1_xboole_0 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('275',plain,
    ( ( k4_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['268','275'])).

thf('277',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['242','245'])).

thf('278',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['267','276','277'])).

thf('279',plain,(
    $false ),
    inference('sup-',[status(thm)],['246','278'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W76x7jbubj
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.78/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.99  % Solved by: fo/fo7.sh
% 0.78/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.99  % done 785 iterations in 0.531s
% 0.78/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.99  % SZS output start Refutation
% 0.78/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.78/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.78/0.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.78/0.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.78/0.99  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.78/0.99  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.78/0.99  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.78/0.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.78/0.99  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.78/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.78/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.78/0.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.78/0.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.78/0.99  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.78/0.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.78/0.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.78/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.78/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.78/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.78/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.78/0.99  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.78/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.78/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.99  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.78/0.99  thf(d3_struct_0, axiom,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.78/0.99  thf('0', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf(t62_tops_2, conjecture,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( l1_struct_0 @ A ) =>
% 0.78/0.99       ( ![B:$i]:
% 0.78/0.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.78/0.99           ( ![C:$i]:
% 0.78/0.99             ( ( ( v1_funct_1 @ C ) & 
% 0.78/0.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.78/0.99                 ( m1_subset_1 @
% 0.78/0.99                   C @ 
% 0.78/0.99                   ( k1_zfmisc_1 @
% 0.78/0.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.78/0.99               ( ( ( ( k2_relset_1 @
% 0.78/0.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.78/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.78/0.99                   ( v2_funct_1 @ C ) ) =>
% 0.78/0.99                 ( ( ( k1_relset_1 @
% 0.78/0.99                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.78/0.99                       ( k2_tops_2 @
% 0.78/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.78/0.99                     ( k2_struct_0 @ B ) ) & 
% 0.78/0.99                   ( ( k2_relset_1 @
% 0.78/0.99                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.78/0.99                       ( k2_tops_2 @
% 0.78/0.99                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.78/0.99                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.78/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.99    (~( ![A:$i]:
% 0.78/0.99        ( ( l1_struct_0 @ A ) =>
% 0.78/0.99          ( ![B:$i]:
% 0.78/0.99            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.78/0.99              ( ![C:$i]:
% 0.78/0.99                ( ( ( v1_funct_1 @ C ) & 
% 0.78/0.99                    ( v1_funct_2 @
% 0.78/0.99                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.78/0.99                    ( m1_subset_1 @
% 0.78/0.99                      C @ 
% 0.78/0.99                      ( k1_zfmisc_1 @
% 0.78/0.99                        ( k2_zfmisc_1 @
% 0.78/0.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.78/0.99                  ( ( ( ( k2_relset_1 @
% 0.78/0.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.78/0.99                        ( k2_struct_0 @ B ) ) & 
% 0.78/0.99                      ( v2_funct_1 @ C ) ) =>
% 0.78/0.99                    ( ( ( k1_relset_1 @
% 0.78/0.99                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.78/0.99                          ( k2_tops_2 @
% 0.78/0.99                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.78/0.99                        ( k2_struct_0 @ B ) ) & 
% 0.78/0.99                      ( ( k2_relset_1 @
% 0.78/0.99                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.78/0.99                          ( k2_tops_2 @
% 0.78/0.99                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.78/0.99                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.78/0.99    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.78/0.99  thf('1', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('2', plain,
% 0.78/0.99      (((m1_subset_1 @ sk_C @ 
% 0.78/0.99         (k1_zfmisc_1 @ 
% 0.78/0.99          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.78/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['0', '1'])).
% 0.78/0.99  thf('3', plain, ((l1_struct_0 @ sk_B)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('4', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.78/0.99      inference('demod', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('5', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(redefinition_k2_relset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.78/0.99  thf('6', plain,
% 0.78/0.99      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.78/0.99         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.78/0.99          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.78/0.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.78/0.99  thf('7', plain,
% 0.78/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.78/0.99         = (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['5', '6'])).
% 0.78/0.99  thf('8', plain,
% 0.78/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.78/0.99         = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('9', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf('10', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.78/0.99      inference('demod', [status(thm)], ['4', '9'])).
% 0.78/0.99  thf('11', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(cc5_funct_2, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.78/0.99       ( ![C:$i]:
% 0.78/0.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.99           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.78/0.99             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.78/0.99  thf('12', plain,
% 0.78/0.99      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.78/0.99          | (v1_partfun1 @ X39 @ X40)
% 0.78/0.99          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.78/0.99          | ~ (v1_funct_1 @ X39)
% 0.78/0.99          | (v1_xboole_0 @ X41))),
% 0.78/0.99      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.78/0.99  thf('13', plain,
% 0.78/0.99      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.78/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.78/0.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.78/0.99        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['11', '12'])).
% 0.78/0.99  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('15', plain,
% 0.78/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('16', plain,
% 0.78/0.99      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.78/0.99        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.78/0.99      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.78/0.99  thf('17', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(dt_k2_relset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.99       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.78/0.99  thf('18', plain,
% 0.78/0.99      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.78/0.99         ((m1_subset_1 @ (k2_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X25))
% 0.78/0.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.78/0.99      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.78/0.99  thf('19', plain,
% 0.78/0.99      ((m1_subset_1 @ 
% 0.78/0.99        (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['17', '18'])).
% 0.78/0.99  thf('20', plain,
% 0.78/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.78/0.99         = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('21', plain,
% 0.78/0.99      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.78/0.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.78/0.99      inference('demod', [status(thm)], ['19', '20'])).
% 0.78/0.99  thf(l13_xboole_0, axiom,
% 0.78/0.99    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.78/0.99  thf('22', plain,
% 0.78/0.99      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.78/0.99      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.99  thf(t113_zfmisc_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.78/0.99       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.78/0.99  thf('23', plain,
% 0.78/0.99      (![X5 : $i, X6 : $i]:
% 0.78/0.99         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.78/0.99      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.78/0.99  thf('24', plain,
% 0.78/0.99      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.78/0.99      inference('simplify', [status(thm)], ['23'])).
% 0.78/0.99  thf(cc4_relset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( v1_xboole_0 @ A ) =>
% 0.78/0.99       ( ![C:$i]:
% 0.78/0.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.78/0.99           ( v1_xboole_0 @ C ) ) ) ))).
% 0.78/0.99  thf('25', plain,
% 0.78/0.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.78/0.99         (~ (v1_xboole_0 @ X21)
% 0.78/0.99          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.78/0.99          | (v1_xboole_0 @ X22))),
% 0.78/0.99      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.78/0.99  thf('26', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.78/0.99          | (v1_xboole_0 @ X1)
% 0.78/0.99          | ~ (v1_xboole_0 @ X0))),
% 0.78/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.78/0.99  thf('27', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.78/0.99          | ~ (v1_xboole_0 @ X0)
% 0.78/0.99          | ~ (v1_xboole_0 @ X2)
% 0.78/0.99          | (v1_xboole_0 @ X1))),
% 0.78/0.99      inference('sup-', [status(thm)], ['22', '26'])).
% 0.78/0.99  thf('28', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         ((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.78/0.99          | ~ (v1_xboole_0 @ X0)
% 0.78/0.99          | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['21', '27'])).
% 0.78/0.99  thf('29', plain,
% 0.78/0.99      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.78/0.99        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.78/0.99      inference('condensation', [status(thm)], ['28'])).
% 0.78/0.99  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf('31', plain,
% 0.78/0.99      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.78/0.99        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.78/0.99      inference('demod', [status(thm)], ['29', '30'])).
% 0.78/0.99  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf(fc5_struct_0, axiom,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.78/0.99       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.78/0.99  thf('33', plain,
% 0.78/0.99      (![X48 : $i]:
% 0.78/0.99         (~ (v1_xboole_0 @ (k2_struct_0 @ X48))
% 0.78/0.99          | ~ (l1_struct_0 @ X48)
% 0.78/0.99          | (v2_struct_0 @ X48))),
% 0.78/0.99      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.78/0.99  thf('34', plain,
% 0.78/0.99      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.78/0.99        | (v2_struct_0 @ sk_B)
% 0.78/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup-', [status(thm)], ['32', '33'])).
% 0.78/0.99  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('36', plain,
% 0.78/0.99      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.78/0.99      inference('demod', [status(thm)], ['34', '35'])).
% 0.78/0.99  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('38', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('clc', [status(thm)], ['36', '37'])).
% 0.78/0.99  thf('39', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.78/0.99      inference('clc', [status(thm)], ['31', '38'])).
% 0.78/0.99  thf('40', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('clc', [status(thm)], ['16', '39'])).
% 0.78/0.99  thf(d4_partfun1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.78/0.99       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.78/0.99  thf('41', plain,
% 0.78/0.99      (![X42 : $i, X43 : $i]:
% 0.78/0.99         (~ (v1_partfun1 @ X43 @ X42)
% 0.78/0.99          | ((k1_relat_1 @ X43) = (X42))
% 0.78/0.99          | ~ (v4_relat_1 @ X43 @ X42)
% 0.78/0.99          | ~ (v1_relat_1 @ X43))),
% 0.78/0.99      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.78/0.99  thf('42', plain,
% 0.78/0.99      ((~ (v1_relat_1 @ sk_C)
% 0.78/0.99        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.78/0.99        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['40', '41'])).
% 0.78/0.99  thf('43', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(cc2_relat_1, axiom,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( v1_relat_1 @ A ) =>
% 0.78/0.99       ( ![B:$i]:
% 0.78/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.78/0.99  thf('44', plain,
% 0.78/0.99      (![X7 : $i, X8 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.78/0.99          | (v1_relat_1 @ X7)
% 0.78/0.99          | ~ (v1_relat_1 @ X8))),
% 0.78/0.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.78/0.99  thf('45', plain,
% 0.78/0.99      ((~ (v1_relat_1 @ 
% 0.78/0.99           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.78/0.99        | (v1_relat_1 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['43', '44'])).
% 0.78/0.99  thf(fc6_relat_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.78/0.99  thf('46', plain,
% 0.78/0.99      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.78/0.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.78/0.99  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.78/0.99      inference('demod', [status(thm)], ['45', '46'])).
% 0.78/0.99  thf('48', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(cc2_relset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.99       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.78/0.99  thf('49', plain,
% 0.78/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.78/0.99         ((v4_relat_1 @ X18 @ X19)
% 0.78/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.78/0.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.78/0.99  thf('50', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('sup-', [status(thm)], ['48', '49'])).
% 0.78/0.99  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['42', '47', '50'])).
% 0.78/0.99  thf('52', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.78/0.99      inference('demod', [status(thm)], ['10', '51'])).
% 0.78/0.99  thf(t31_funct_2, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.78/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.78/0.99       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.78/0.99         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.78/0.99           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.78/0.99           ( m1_subset_1 @
% 0.78/0.99             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.78/0.99  thf('53', plain,
% 0.78/0.99      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.78/0.99         (~ (v2_funct_1 @ X44)
% 0.78/0.99          | ((k2_relset_1 @ X46 @ X45 @ X44) != (X45))
% 0.78/0.99          | (m1_subset_1 @ (k2_funct_1 @ X44) @ 
% 0.78/0.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.78/0.99          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.78/0.99          | ~ (v1_funct_2 @ X44 @ X46 @ X45)
% 0.78/0.99          | ~ (v1_funct_1 @ X44))),
% 0.78/0.99      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.78/0.99  thf('54', plain,
% 0.78/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.78/0.99        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.78/0.99        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.78/0.99           (k1_zfmisc_1 @ 
% 0.78/0.99            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.78/0.99        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99            != (k2_relat_1 @ sk_C))
% 0.78/0.99        | ~ (v2_funct_1 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['52', '53'])).
% 0.78/0.99  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('56', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('57', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('58', plain,
% 0.78/0.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('59', plain,
% 0.78/0.99      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.78/0.99        | ~ (l1_struct_0 @ sk_A))),
% 0.78/0.99      inference('sup+', [status(thm)], ['57', '58'])).
% 0.78/0.99  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('61', plain,
% 0.78/0.99      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.78/0.99      inference('demod', [status(thm)], ['59', '60'])).
% 0.78/0.99  thf('62', plain,
% 0.78/0.99      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.78/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['56', '61'])).
% 0.78/0.99  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('64', plain,
% 0.78/0.99      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('demod', [status(thm)], ['62', '63'])).
% 0.78/0.99  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf('66', plain,
% 0.78/0.99      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['64', '65'])).
% 0.78/0.99  thf('67', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('68', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('clc', [status(thm)], ['16', '39'])).
% 0.78/0.99  thf('69', plain,
% 0.78/0.99      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.78/0.99      inference('sup+', [status(thm)], ['67', '68'])).
% 0.78/0.99  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('71', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['69', '70'])).
% 0.78/0.99  thf('72', plain,
% 0.78/0.99      (![X42 : $i, X43 : $i]:
% 0.78/0.99         (~ (v1_partfun1 @ X43 @ X42)
% 0.78/0.99          | ((k1_relat_1 @ X43) = (X42))
% 0.78/0.99          | ~ (v4_relat_1 @ X43 @ X42)
% 0.78/0.99          | ~ (v1_relat_1 @ X43))),
% 0.78/0.99      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.78/0.99  thf('73', plain,
% 0.78/0.99      ((~ (v1_relat_1 @ sk_C)
% 0.78/0.99        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.78/0.99        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['71', '72'])).
% 0.78/0.99  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.78/0.99      inference('demod', [status(thm)], ['45', '46'])).
% 0.78/0.99  thf('75', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('76', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('77', plain,
% 0.78/0.99      (((m1_subset_1 @ sk_C @ 
% 0.78/0.99         (k1_zfmisc_1 @ 
% 0.78/0.99          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.78/0.99        | ~ (l1_struct_0 @ sk_A))),
% 0.78/0.99      inference('sup+', [status(thm)], ['75', '76'])).
% 0.78/0.99  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('79', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('demod', [status(thm)], ['77', '78'])).
% 0.78/0.99  thf('80', plain,
% 0.78/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.78/0.99         ((v4_relat_1 @ X18 @ X19)
% 0.78/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.78/0.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.78/0.99  thf('81', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.78/0.99      inference('sup-', [status(thm)], ['79', '80'])).
% 0.78/0.99  thf('82', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['73', '74', '81'])).
% 0.78/0.99  thf('83', plain,
% 0.78/0.99      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['66', '82'])).
% 0.78/0.99  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(d9_funct_1, axiom,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.78/0.99       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.78/0.99  thf('85', plain,
% 0.78/0.99      (![X15 : $i]:
% 0.78/0.99         (~ (v2_funct_1 @ X15)
% 0.78/0.99          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 0.78/0.99          | ~ (v1_funct_1 @ X15)
% 0.78/0.99          | ~ (v1_relat_1 @ X15))),
% 0.78/0.99      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.78/0.99  thf('86', plain,
% 0.78/0.99      ((~ (v1_relat_1 @ sk_C)
% 0.78/0.99        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.78/0.99        | ~ (v2_funct_1 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['84', '85'])).
% 0.78/0.99  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.78/0.99      inference('demod', [status(thm)], ['45', '46'])).
% 0.78/0.99  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('89', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.78/0.99  thf('90', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('91', plain,
% 0.78/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.78/0.99         = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('92', plain,
% 0.78/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.78/0.99          = (k2_struct_0 @ sk_B))
% 0.78/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['90', '91'])).
% 0.78/0.99  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('94', plain,
% 0.78/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.78/0.99         = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('demod', [status(thm)], ['92', '93'])).
% 0.78/0.99  thf('95', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf('96', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf('97', plain,
% 0.78/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99         = (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.78/0.99  thf('98', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['42', '47', '50'])).
% 0.78/0.99  thf('99', plain,
% 0.78/0.99      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99         = (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['97', '98'])).
% 0.78/0.99  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('101', plain,
% 0.78/0.99      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.78/0.99         (k1_zfmisc_1 @ 
% 0.78/0.99          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.78/0.99        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['54', '55', '83', '89', '99', '100'])).
% 0.78/0.99  thf('102', plain,
% 0.78/0.99      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.78/0.99      inference('simplify', [status(thm)], ['101'])).
% 0.78/0.99  thf('103', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.78/0.99  thf(d10_xboole_0, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.78/0.99  thf('104', plain,
% 0.78/0.99      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.78/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.78/0.99  thf('105', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.78/0.99      inference('simplify', [status(thm)], ['104'])).
% 0.78/0.99  thf(t177_funct_1, axiom,
% 0.78/0.99    (![A:$i]:
% 0.78/0.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.78/0.99       ( ![B:$i]:
% 0.78/0.99         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.78/0.99           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.78/0.99             ( B ) ) ) ) ))).
% 0.78/0.99  thf('106', plain,
% 0.78/0.99      (![X16 : $i, X17 : $i]:
% 0.78/0.99         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.78/0.99          | ((k9_relat_1 @ (k2_funct_1 @ X17) @ (k9_relat_1 @ X17 @ X16))
% 0.78/0.99              = (X16))
% 0.78/0.99          | ~ (v2_funct_1 @ X17)
% 0.78/0.99          | ~ (v1_funct_1 @ X17)
% 0.78/0.99          | ~ (v1_relat_1 @ X17))),
% 0.78/0.99      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.78/0.99  thf('107', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (v1_relat_1 @ X0)
% 0.78/0.99          | ~ (v1_funct_1 @ X0)
% 0.78/0.99          | ~ (v2_funct_1 @ X0)
% 0.78/0.99          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.78/0.99              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['105', '106'])).
% 0.78/0.99  thf('108', plain,
% 0.78/0.99      ((((k9_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 0.78/0.99          (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))) = (k1_relat_1 @ sk_C))
% 0.78/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.78/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.78/0.99        | ~ (v1_relat_1 @ sk_C))),
% 0.78/0.99      inference('sup+', [status(thm)], ['103', '107'])).
% 0.78/0.99  thf('109', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.78/0.99      inference('sup-', [status(thm)], ['79', '80'])).
% 0.78/0.99  thf(t209_relat_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.78/0.99       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.78/0.99  thf('110', plain,
% 0.78/0.99      (![X13 : $i, X14 : $i]:
% 0.78/0.99         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.78/0.99          | ~ (v4_relat_1 @ X13 @ X14)
% 0.78/0.99          | ~ (v1_relat_1 @ X13))),
% 0.78/0.99      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.78/0.99  thf('111', plain,
% 0.78/0.99      ((~ (v1_relat_1 @ sk_C)
% 0.78/0.99        | ((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['109', '110'])).
% 0.78/0.99  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 0.78/0.99      inference('demod', [status(thm)], ['45', '46'])).
% 0.78/0.99  thf('113', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.78/0.99      inference('demod', [status(thm)], ['111', '112'])).
% 0.78/0.99  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 0.78/0.99      inference('demod', [status(thm)], ['45', '46'])).
% 0.78/0.99  thf(t148_relat_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( v1_relat_1 @ B ) =>
% 0.78/0.99       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.78/0.99  thf('115', plain,
% 0.78/0.99      (![X11 : $i, X12 : $i]:
% 0.78/0.99         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.78/0.99          | ~ (v1_relat_1 @ X11))),
% 0.78/0.99      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.78/0.99  thf('116', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.78/0.99      inference('sup-', [status(thm)], ['114', '115'])).
% 0.78/0.99  thf('117', plain,
% 0.78/0.99      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['113', '116'])).
% 0.78/0.99  thf('118', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['73', '74', '81'])).
% 0.78/0.99  thf('119', plain,
% 0.78/0.99      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['117', '118'])).
% 0.78/0.99  thf('120', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('121', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(dt_k3_relset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.99       ( m1_subset_1 @
% 0.78/0.99         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.78/0.99         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.78/0.99  thf('122', plain,
% 0.78/0.99      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.78/0.99         ((m1_subset_1 @ (k3_relset_1 @ X27 @ X28 @ X29) @ 
% 0.78/0.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.78/0.99          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.78/0.99      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.78/0.99  thf('123', plain,
% 0.78/0.99      ((m1_subset_1 @ 
% 0.78/0.99        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['121', '122'])).
% 0.78/0.99  thf('124', plain,
% 0.78/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.78/0.99         ((v4_relat_1 @ X18 @ X19)
% 0.78/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.78/0.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.78/0.99  thf('125', plain,
% 0.78/0.99      ((v4_relat_1 @ 
% 0.78/0.99        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.78/0.99        (u1_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup-', [status(thm)], ['123', '124'])).
% 0.78/0.99  thf('126', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(redefinition_k3_relset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.99       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.78/0.99  thf('127', plain,
% 0.78/0.99      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.78/0.99         (((k3_relset_1 @ X37 @ X38 @ X36) = (k4_relat_1 @ X36))
% 0.78/0.99          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.78/0.99      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.78/0.99  thf('128', plain,
% 0.78/0.99      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.78/0.99         = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['126', '127'])).
% 0.78/0.99  thf('129', plain,
% 0.78/0.99      ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.78/0.99      inference('demod', [status(thm)], ['125', '128'])).
% 0.78/0.99  thf('130', plain,
% 0.78/0.99      (((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.78/0.99        | ~ (l1_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['120', '129'])).
% 0.78/0.99  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf('132', plain, ((l1_struct_0 @ sk_B)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('133', plain, ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.78/0.99  thf('134', plain,
% 0.78/0.99      (![X13 : $i, X14 : $i]:
% 0.78/0.99         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.78/0.99          | ~ (v4_relat_1 @ X13 @ X14)
% 0.78/0.99          | ~ (v1_relat_1 @ X13))),
% 0.78/0.99      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.78/0.99  thf('135', plain,
% 0.78/0.99      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.78/0.99        | ((k4_relat_1 @ sk_C)
% 0.78/0.99            = (k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['133', '134'])).
% 0.78/0.99  thf('136', plain,
% 0.78/0.99      ((m1_subset_1 @ 
% 0.78/0.99        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['121', '122'])).
% 0.78/0.99  thf('137', plain,
% 0.78/0.99      (![X7 : $i, X8 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.78/0.99          | (v1_relat_1 @ X7)
% 0.78/0.99          | ~ (v1_relat_1 @ X8))),
% 0.78/0.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.78/0.99  thf('138', plain,
% 0.78/0.99      ((~ (v1_relat_1 @ 
% 0.78/0.99           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.78/0.99        | (v1_relat_1 @ 
% 0.78/0.99           (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['136', '137'])).
% 0.78/0.99  thf('139', plain,
% 0.78/0.99      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.78/0.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.78/0.99  thf('140', plain,
% 0.78/0.99      ((v1_relat_1 @ 
% 0.78/0.99        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['138', '139'])).
% 0.78/0.99  thf('141', plain,
% 0.78/0.99      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.78/0.99         = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['126', '127'])).
% 0.78/0.99  thf('142', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['140', '141'])).
% 0.78/0.99  thf('143', plain,
% 0.78/0.99      (((k4_relat_1 @ sk_C)
% 0.78/0.99         = (k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['135', '142'])).
% 0.78/0.99  thf('144', plain,
% 0.78/0.99      (![X11 : $i, X12 : $i]:
% 0.78/0.99         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.78/0.99          | ~ (v1_relat_1 @ X11))),
% 0.78/0.99      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.78/0.99  thf('145', plain,
% 0.78/0.99      ((((k2_relat_1 @ (k4_relat_1 @ sk_C))
% 0.78/0.99          = (k9_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 0.78/0.99        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['143', '144'])).
% 0.78/0.99  thf('146', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['140', '141'])).
% 0.78/0.99  thf('147', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C))
% 0.78/0.99         = (k9_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['145', '146'])).
% 0.78/0.99  thf('148', plain, ((v2_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.78/0.99      inference('demod', [status(thm)], ['45', '46'])).
% 0.78/0.99  thf('151', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['108', '119', '147', '148', '149', '150'])).
% 0.78/0.99  thf('152', plain,
% 0.78/0.99      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ 
% 0.78/0.99          (k2_relat_1 @ (k4_relat_1 @ sk_C)))))),
% 0.78/0.99      inference('demod', [status(thm)], ['102', '151'])).
% 0.78/0.99  thf('153', plain,
% 0.78/0.99      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.78/0.99          | (v1_partfun1 @ X39 @ X40)
% 0.78/0.99          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.78/0.99          | ~ (v1_funct_1 @ X39)
% 0.78/0.99          | (v1_xboole_0 @ X41))),
% 0.78/0.99      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.78/0.99  thf('154', plain,
% 0.78/0.99      (((v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.78/0.99        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.78/0.99        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.78/0.99             (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.78/0.99        | (v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['152', '153'])).
% 0.78/0.99  thf('155', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.78/0.99      inference('demod', [status(thm)], ['10', '51'])).
% 0.78/0.99  thf('156', plain,
% 0.78/0.99      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.78/0.99         (~ (v2_funct_1 @ X44)
% 0.78/0.99          | ((k2_relset_1 @ X46 @ X45 @ X44) != (X45))
% 0.78/0.99          | (v1_funct_1 @ (k2_funct_1 @ X44))
% 0.78/0.99          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.78/0.99          | ~ (v1_funct_2 @ X44 @ X46 @ X45)
% 0.78/0.99          | ~ (v1_funct_1 @ X44))),
% 0.78/0.99      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.78/0.99  thf('157', plain,
% 0.78/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.78/0.99        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.78/0.99        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.78/0.99        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99            != (k2_relat_1 @ sk_C))
% 0.78/0.99        | ~ (v2_funct_1 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['155', '156'])).
% 0.78/0.99  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('159', plain,
% 0.78/0.99      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['66', '82'])).
% 0.78/0.99  thf('160', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.78/0.99  thf('161', plain,
% 0.78/0.99      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99         = (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['97', '98'])).
% 0.78/0.99  thf('162', plain, ((v2_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('163', plain,
% 0.78/0.99      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.78/0.99        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['157', '158', '159', '160', '161', '162'])).
% 0.78/0.99  thf('164', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('simplify', [status(thm)], ['163'])).
% 0.78/0.99  thf('165', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.78/0.99      inference('demod', [status(thm)], ['10', '51'])).
% 0.78/0.99  thf('166', plain,
% 0.78/0.99      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.78/0.99         (~ (v2_funct_1 @ X44)
% 0.78/0.99          | ((k2_relset_1 @ X46 @ X45 @ X44) != (X45))
% 0.78/0.99          | (v1_funct_2 @ (k2_funct_1 @ X44) @ X45 @ X46)
% 0.78/0.99          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.78/0.99          | ~ (v1_funct_2 @ X44 @ X46 @ X45)
% 0.78/0.99          | ~ (v1_funct_1 @ X44))),
% 0.78/0.99      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.78/0.99  thf('167', plain,
% 0.78/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.78/0.99        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.78/0.99        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.78/0.99           (k1_relat_1 @ sk_C))
% 0.78/0.99        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99            != (k2_relat_1 @ sk_C))
% 0.78/0.99        | ~ (v2_funct_1 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['165', '166'])).
% 0.78/0.99  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('169', plain,
% 0.78/0.99      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['66', '82'])).
% 0.78/0.99  thf('170', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.78/0.99  thf('171', plain,
% 0.78/0.99      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99         = (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['97', '98'])).
% 0.78/0.99  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('173', plain,
% 0.78/0.99      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.78/0.99         (k1_relat_1 @ sk_C))
% 0.78/0.99        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['167', '168', '169', '170', '171', '172'])).
% 0.78/0.99  thf('174', plain,
% 0.78/0.99      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.78/0.99        (k1_relat_1 @ sk_C))),
% 0.78/0.99      inference('simplify', [status(thm)], ['173'])).
% 0.78/0.99  thf('175', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['108', '119', '147', '148', '149', '150'])).
% 0.78/0.99  thf('176', plain,
% 0.78/0.99      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.78/0.99        (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['174', '175'])).
% 0.78/0.99  thf('177', plain,
% 0.78/0.99      (((v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.78/0.99        | (v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['154', '164', '176'])).
% 0.78/0.99  thf('178', plain,
% 0.78/0.99      (![X42 : $i, X43 : $i]:
% 0.78/0.99         (~ (v1_partfun1 @ X43 @ X42)
% 0.78/0.99          | ((k1_relat_1 @ X43) = (X42))
% 0.78/0.99          | ~ (v4_relat_1 @ X43 @ X42)
% 0.78/0.99          | ~ (v1_relat_1 @ X43))),
% 0.78/0.99      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.78/0.99  thf('179', plain,
% 0.78/0.99      (((v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.78/0.99        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.78/0.99        | ~ (v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.78/0.99        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['177', '178'])).
% 0.78/0.99  thf('180', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['140', '141'])).
% 0.78/0.99  thf('181', plain, ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.78/0.99  thf('182', plain,
% 0.78/0.99      (((v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.78/0.99        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.78/0.99  thf('183', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('184', plain,
% 0.78/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          != (k2_struct_0 @ sk_B))
% 0.78/0.99        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99            != (k2_struct_0 @ sk_A)))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('185', plain,
% 0.78/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          != (k2_struct_0 @ sk_B)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_B))))),
% 0.78/0.99      inference('split', [status(esa)], ['184'])).
% 0.78/0.99  thf('186', plain,
% 0.78/0.99      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99           != (k2_struct_0 @ sk_B))
% 0.78/0.99         | ~ (l1_struct_0 @ sk_B)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_B))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['183', '185'])).
% 0.78/0.99  thf('187', plain, ((l1_struct_0 @ sk_B)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('188', plain,
% 0.78/0.99      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          != (k2_struct_0 @ sk_B)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_B))))),
% 0.78/0.99      inference('demod', [status(thm)], ['186', '187'])).
% 0.78/0.99  thf('189', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['42', '47', '50'])).
% 0.78/0.99  thf('190', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['108', '119', '147', '148', '149', '150'])).
% 0.78/0.99  thf('191', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['189', '190'])).
% 0.78/0.99  thf('192', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['189', '190'])).
% 0.78/0.99  thf('193', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf('194', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.78/0.99      inference('demod', [status(thm)], ['10', '51'])).
% 0.78/0.99  thf(d4_tops_2, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.78/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.78/0.99       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.78/0.99         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.78/0.99  thf('195', plain,
% 0.78/0.99      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.78/0.99         (((k2_relset_1 @ X50 @ X49 @ X51) != (X49))
% 0.78/0.99          | ~ (v2_funct_1 @ X51)
% 0.78/0.99          | ((k2_tops_2 @ X50 @ X49 @ X51) = (k2_funct_1 @ X51))
% 0.78/0.99          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.78/0.99          | ~ (v1_funct_2 @ X51 @ X50 @ X49)
% 0.78/0.99          | ~ (v1_funct_1 @ X51))),
% 0.78/0.99      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.78/0.99  thf('196', plain,
% 0.78/0.99      ((~ (v1_funct_1 @ sk_C)
% 0.78/0.99        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.78/0.99        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99            = (k2_funct_1 @ sk_C))
% 0.78/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.78/0.99        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99            != (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['194', '195'])).
% 0.78/0.99  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('198', plain,
% 0.78/0.99      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['66', '82'])).
% 0.78/0.99  thf('199', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.78/0.99  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('201', plain,
% 0.78/0.99      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99         = (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['97', '98'])).
% 0.78/0.99  thf('202', plain,
% 0.78/0.99      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99          = (k4_relat_1 @ sk_C))
% 0.78/0.99        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['196', '197', '198', '199', '200', '201'])).
% 0.78/0.99  thf('203', plain,
% 0.78/0.99      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.78/0.99         = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('simplify', [status(thm)], ['202'])).
% 0.78/0.99  thf('204', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['108', '119', '147', '148', '149', '150'])).
% 0.78/0.99  thf('205', plain,
% 0.78/0.99      (((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.78/0.99         (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['203', '204'])).
% 0.78/0.99  thf('206', plain,
% 0.78/0.99      ((m1_subset_1 @ 
% 0.78/0.99        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['121', '122'])).
% 0.78/0.99  thf('207', plain,
% 0.78/0.99      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.78/0.99         = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['126', '127'])).
% 0.78/0.99  thf('208', plain,
% 0.78/0.99      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.78/0.99      inference('demod', [status(thm)], ['206', '207'])).
% 0.78/0.99  thf('209', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['189', '190'])).
% 0.78/0.99  thf('210', plain,
% 0.78/0.99      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.78/0.99          (k2_relat_1 @ (k4_relat_1 @ sk_C)))))),
% 0.78/0.99      inference('demod', [status(thm)], ['208', '209'])).
% 0.78/0.99  thf(redefinition_k1_relset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i,C:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.78/0.99  thf('211', plain,
% 0.78/0.99      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.78/0.99         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.78/0.99          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.78/0.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.78/0.99  thf('212', plain,
% 0.78/0.99      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.78/0.99         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 0.78/0.99         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['210', '211'])).
% 0.78/0.99  thf('213', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf('214', plain,
% 0.78/0.99      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_B))))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['188', '191', '192', '193', '205', '212', '213'])).
% 0.78/0.99  thf('215', plain,
% 0.78/0.99      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.78/0.99          (k2_relat_1 @ (k4_relat_1 @ sk_C)))))),
% 0.78/0.99      inference('demod', [status(thm)], ['208', '209'])).
% 0.78/0.99  thf('216', plain,
% 0.78/0.99      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.78/0.99         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.78/0.99          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.78/0.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.78/0.99  thf('217', plain,
% 0.78/0.99      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.78/0.99         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 0.78/0.99         = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['215', '216'])).
% 0.78/0.99  thf('218', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['73', '74', '81'])).
% 0.78/0.99  thf('219', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('220', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('221', plain,
% 0.78/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          != (k2_struct_0 @ sk_A)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('split', [status(esa)], ['184'])).
% 0.78/0.99  thf('222', plain,
% 0.78/0.99      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99           != (k2_struct_0 @ sk_A))
% 0.78/0.99         | ~ (l1_struct_0 @ sk_A)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['220', '221'])).
% 0.78/0.99  thf('223', plain, ((l1_struct_0 @ sk_A)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('224', plain,
% 0.78/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          != (k2_struct_0 @ sk_A)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('demod', [status(thm)], ['222', '223'])).
% 0.78/0.99  thf('225', plain,
% 0.78/0.99      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99           != (k2_struct_0 @ sk_A))
% 0.78/0.99         | ~ (l1_struct_0 @ sk_B)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['219', '224'])).
% 0.78/0.99  thf('226', plain, ((l1_struct_0 @ sk_B)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('227', plain,
% 0.78/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          != (k2_struct_0 @ sk_A)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('demod', [status(thm)], ['225', '226'])).
% 0.78/0.99  thf('228', plain,
% 0.78/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          != (k2_struct_0 @ sk_A)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['218', '227'])).
% 0.78/0.99  thf('229', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.78/0.99      inference('sup+', [status(thm)], ['7', '8'])).
% 0.78/0.99  thf('230', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['73', '74', '81'])).
% 0.78/0.99  thf('231', plain,
% 0.78/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.78/0.99          != (k1_relat_1 @ sk_C)))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('demod', [status(thm)], ['228', '229', '230'])).
% 0.78/0.99  thf('232', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['189', '190'])).
% 0.78/0.99  thf('233', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['108', '119', '147', '148', '149', '150'])).
% 0.78/0.99  thf('234', plain,
% 0.78/0.99      (((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.78/0.99         (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['203', '204'])).
% 0.78/0.99  thf('235', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['108', '119', '147', '148', '149', '150'])).
% 0.78/0.99  thf('236', plain,
% 0.78/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.78/0.99          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 0.78/0.99          != (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('demod', [status(thm)], ['231', '232', '233', '234', '235'])).
% 0.78/0.99  thf('237', plain,
% 0.78/0.99      ((((k2_relat_1 @ (k4_relat_1 @ sk_C))
% 0.78/0.99          != (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 0.78/0.99         <= (~
% 0.78/0.99             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99                = (k2_struct_0 @ sk_A))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['217', '236'])).
% 0.78/0.99  thf('238', plain,
% 0.78/0.99      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          = (k2_struct_0 @ sk_A)))),
% 0.78/0.99      inference('simplify', [status(thm)], ['237'])).
% 0.78/0.99  thf('239', plain,
% 0.78/0.99      (~
% 0.78/0.99       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          = (k2_struct_0 @ sk_B))) | 
% 0.78/0.99       ~
% 0.78/0.99       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          = (k2_struct_0 @ sk_A)))),
% 0.78/0.99      inference('split', [status(esa)], ['184'])).
% 0.78/0.99  thf('240', plain,
% 0.78/0.99      (~
% 0.78/0.99       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.99          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.78/0.99          = (k2_struct_0 @ sk_B)))),
% 0.78/0.99      inference('sat_resolution*', [status(thm)], ['238', '239'])).
% 0.78/0.99  thf('241', plain,
% 0.78/0.99      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('simpl_trail', [status(thm)], ['214', '240'])).
% 0.78/0.99  thf('242', plain, ((v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.78/0.99      inference('simplify_reflect-', [status(thm)], ['182', '241'])).
% 0.78/0.99  thf('243', plain, ((v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.78/0.99      inference('simplify_reflect-', [status(thm)], ['182', '241'])).
% 0.78/0.99  thf('244', plain,
% 0.78/0.99      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.78/0.99      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.99  thf('245', plain, (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_xboole_0))),
% 0.78/0.99      inference('sup-', [status(thm)], ['243', '244'])).
% 0.78/0.99  thf('246', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.99      inference('demod', [status(thm)], ['242', '245'])).
% 0.78/0.99  thf('247', plain,
% 0.78/0.99      (![X47 : $i]:
% 0.78/0.99         (((k2_struct_0 @ X47) = (u1_struct_0 @ X47)) | ~ (l1_struct_0 @ X47))),
% 0.78/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.78/0.99  thf('248', plain,
% 0.78/0.99      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.78/0.99      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.99  thf('249', plain,
% 0.78/0.99      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.78/0.99      inference('simplify', [status(thm)], ['23'])).
% 0.78/0.99  thf('250', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.78/0.99      inference('sup+', [status(thm)], ['248', '249'])).
% 0.78/0.99  thf('251', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_C @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('252', plain,
% 0.78/0.99      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.78/0.99        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.99      inference('sup+', [status(thm)], ['250', '251'])).
% 0.78/0.99  thf('253', plain,
% 0.78/0.99      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.78/0.99        | ~ (l1_struct_0 @ sk_A)
% 0.78/0.99        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['247', '252'])).
% 0.78/0.99  thf('254', plain, ((l1_struct_0 @ sk_A)),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('255', plain,
% 0.78/0.99      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.78/0.99        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.78/0.99      inference('demod', [status(thm)], ['253', '254'])).
% 0.78/0.99  thf('256', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.78/0.99      inference('demod', [status(thm)], ['73', '74', '81'])).
% 0.78/0.99  thf('257', plain,
% 0.78/0.99      ((~ (v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.78/0.99        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.78/0.99      inference('demod', [status(thm)], ['255', '256'])).
% 0.78/0.99  thf('258', plain,
% 0.78/0.99      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)],
% 0.78/0.99                ['108', '119', '147', '148', '149', '150'])).
% 0.78/0.99  thf('259', plain,
% 0.78/0.99      ((~ (v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.78/0.99        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.78/0.99      inference('demod', [status(thm)], ['257', '258'])).
% 0.78/0.99  thf('260', plain, ((v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.78/0.99      inference('simplify_reflect-', [status(thm)], ['182', '241'])).
% 0.78/0.99  thf('261', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.78/0.99      inference('demod', [status(thm)], ['259', '260'])).
% 0.78/0.99  thf('262', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.78/0.99          | (v1_xboole_0 @ X1)
% 0.78/0.99          | ~ (v1_xboole_0 @ X0))),
% 0.78/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.78/0.99  thf('263', plain,
% 0.78/0.99      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ sk_C))),
% 0.78/0.99      inference('sup-', [status(thm)], ['261', '262'])).
% 0.78/0.99  thf('264', plain,
% 0.78/0.99      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.78/0.99      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.99  thf('265', plain,
% 0.78/0.99      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_C) = (k1_xboole_0)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['263', '264'])).
% 0.78/0.99  thf('266', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.78/0.99      inference('clc', [status(thm)], ['36', '37'])).
% 0.78/0.99  thf('267', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.78/0.99      inference('sup-', [status(thm)], ['265', '266'])).
% 0.78/0.99  thf('268', plain, (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_xboole_0))),
% 0.78/0.99      inference('sup-', [status(thm)], ['243', '244'])).
% 0.78/0.99  thf('269', plain,
% 0.78/0.99      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.78/0.99        (k1_zfmisc_1 @ 
% 0.78/0.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.78/0.99          (k2_relat_1 @ (k4_relat_1 @ sk_C)))))),
% 0.78/0.99      inference('demod', [status(thm)], ['208', '209'])).
% 0.78/0.99  thf('270', plain,
% 0.78/0.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.78/0.99         (~ (v1_xboole_0 @ X21)
% 0.78/0.99          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.78/0.99          | (v1_xboole_0 @ X22))),
% 0.78/0.99      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.78/0.99  thf('271', plain,
% 0.78/0.99      (((v1_xboole_0 @ (k4_relat_1 @ sk_C))
% 0.78/0.99        | ~ (v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['269', '270'])).
% 0.78/0.99  thf('272', plain, ((v1_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.78/0.99      inference('simplify_reflect-', [status(thm)], ['182', '241'])).
% 0.78/0.99  thf('273', plain, ((v1_xboole_0 @ (k4_relat_1 @ sk_C))),
% 0.78/0.99      inference('demod', [status(thm)], ['271', '272'])).
% 0.78/0.99  thf('274', plain,
% 0.78/0.99      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.78/0.99      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.99  thf('275', plain, (((k4_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.78/0.99      inference('sup-', [status(thm)], ['273', '274'])).
% 0.78/0.99  thf('276', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.99      inference('demod', [status(thm)], ['268', '275'])).
% 0.78/0.99  thf('277', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.99      inference('demod', [status(thm)], ['242', '245'])).
% 0.78/0.99  thf('278', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.78/0.99      inference('demod', [status(thm)], ['267', '276', '277'])).
% 0.78/0.99  thf('279', plain, ($false), inference('sup-', [status(thm)], ['246', '278'])).
% 0.78/0.99  
% 0.78/0.99  % SZS output end Refutation
% 0.78/0.99  
% 0.78/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
