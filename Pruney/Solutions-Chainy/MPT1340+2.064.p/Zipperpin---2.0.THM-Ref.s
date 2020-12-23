%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GXLHB0V6Ya

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:17 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  335 (1930 expanded)
%              Number of leaves         :   51 ( 592 expanded)
%              Depth                    :   31
%              Number of atoms          : 3233 (38722 expanded)
%              Number of equality atoms :  179 (1097 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','26','29'])).

thf('31',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','50'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('52',plain,(
    ! [X38: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('53',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','57'])).

thf('59',plain,(
    ! [X38: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('60',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['13','64'])).

thf('66',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

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

thf('72',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_tops_2 @ X40 @ X39 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('77',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['81','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','79','80','89'])).

thf('91',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['66','91','92'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X10: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('95',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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

thf('97',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('101',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('102',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['95','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_tops_2 @ X40 @ X39 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('111',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('121',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X33 ) @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X10: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('134',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('135',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('138',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k10_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('139',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('141',plain,(
    ! [X36: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('142',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X36: $i] :
      ( ( v1_funct_2 @ X36 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('145',plain,(
    ! [X36: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('146',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('155',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('159',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['139','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['137','164'])).

thf('166',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('167',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('170',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('172',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['170','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('177',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('178',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('179',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176','177','178'])).

thf('180',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('181',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('182',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('184',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','184'])).

thf('186',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('187',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('189',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','189','190','191','192'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('194',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('195',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k2_funct_1 @ X17 ) )
      | ( ( k5_relat_1 @ X16 @ X17 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['193','197'])).

thf('199',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('200',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('204',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('205',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('208',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('209',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['205','206','207','208','209'])).

thf('211',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('213',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('215',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['117'])).

thf('217',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('218',plain,
    ( ( ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['198','199','200','201','202','215','216','217'])).

thf('219',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','189','190','191','192'])).

thf('221',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('222',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k9_relat_1 @ X11 @ X12 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X11 ) @ X12 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('223',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['221','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['220','226'])).

thf('228',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('229',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('230',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('232',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('234',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['232','233'])).

thf('235',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('236',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('238',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('240',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['227','238','239','240','241'])).

thf('243',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['219','242'])).

thf('244',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['132','244'])).

thf('246',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('247',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['245','246','247','248'])).

thf('250',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','118','131','249'])).

thf('251',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('252',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('253',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','189','190','191','192'])).

thf('255',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['250','255'])).

thf('257',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['94','257'])).

thf('259',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('260',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['258','259','260','261'])).

thf('263',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('264',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('265',plain,(
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

thf('266',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_funct_2 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('267',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['267','268','269'])).

thf('271',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('272',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('273',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['270','271','272','273'])).

thf('275',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['264','274'])).

thf('276',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('278',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['275','276','277'])).

thf('279',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['263','278'])).

thf('280',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['279','280'])).

thf('282',plain,(
    $false ),
    inference(demod,[status(thm)],['93','262','281'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GXLHB0V6Ya
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:54:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 650 iterations in 0.260s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.52/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.52/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.52/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.52/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.73  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.52/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.52/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.52/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.52/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.52/0.73  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.52/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.73  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.73  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.52/0.73  thf(d3_struct_0, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf(t64_tops_2, conjecture,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( l1_struct_0 @ A ) =>
% 0.52/0.73       ( ![B:$i]:
% 0.52/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.52/0.73           ( ![C:$i]:
% 0.52/0.73             ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.73                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.73                 ( m1_subset_1 @
% 0.52/0.73                   C @ 
% 0.52/0.73                   ( k1_zfmisc_1 @
% 0.52/0.73                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.73               ( ( ( ( k2_relset_1 @
% 0.52/0.73                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.52/0.73                     ( k2_struct_0 @ B ) ) & 
% 0.52/0.73                   ( v2_funct_1 @ C ) ) =>
% 0.52/0.73                 ( r2_funct_2 @
% 0.52/0.73                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.52/0.73                   ( k2_tops_2 @
% 0.52/0.73                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.52/0.73                     ( k2_tops_2 @
% 0.52/0.73                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.52/0.73                   C ) ) ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i]:
% 0.52/0.73        ( ( l1_struct_0 @ A ) =>
% 0.52/0.73          ( ![B:$i]:
% 0.52/0.73            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.52/0.73              ( ![C:$i]:
% 0.52/0.73                ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.73                    ( v1_funct_2 @
% 0.52/0.73                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.73                    ( m1_subset_1 @
% 0.52/0.73                      C @ 
% 0.52/0.73                      ( k1_zfmisc_1 @
% 0.52/0.73                        ( k2_zfmisc_1 @
% 0.52/0.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.73                  ( ( ( ( k2_relset_1 @
% 0.52/0.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.52/0.73                        ( k2_struct_0 @ B ) ) & 
% 0.52/0.73                      ( v2_funct_1 @ C ) ) =>
% 0.52/0.73                    ( r2_funct_2 @
% 0.52/0.73                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.52/0.73                      ( k2_tops_2 @
% 0.52/0.73                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.52/0.73                        ( k2_tops_2 @
% 0.52/0.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.52/0.73                      C ) ) ) ) ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.52/0.73  thf('4', plain,
% 0.52/0.73      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.52/0.73          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.52/0.73          sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.52/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.73            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.52/0.73           sk_C)
% 0.52/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.73  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.52/0.73          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.52/0.73          sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.52/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.73            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.52/0.73           sk_C)
% 0.52/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['2', '7'])).
% 0.52/0.73  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.52/0.73          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.52/0.73          sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['8', '9'])).
% 0.52/0.73  thf('11', plain,
% 0.52/0.73      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.52/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.73            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.52/0.73           sk_C)
% 0.52/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['1', '10'])).
% 0.52/0.73  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('13', plain,
% 0.52/0.73      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.52/0.73          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.52/0.73          sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(cc5_funct_2, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.73       ( ![C:$i]:
% 0.52/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.52/0.73             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.52/0.73          | (v1_partfun1 @ X24 @ X25)
% 0.52/0.73          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.52/0.73          | ~ (v1_funct_1 @ X24)
% 0.52/0.73          | (v1_xboole_0 @ X26))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.73        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.73  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.52/0.73  thf(d4_partfun1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.73       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (![X27 : $i, X28 : $i]:
% 0.52/0.73         (~ (v1_partfun1 @ X28 @ X27)
% 0.52/0.73          | ((k1_relat_1 @ X28) = (X27))
% 0.52/0.73          | ~ (v4_relat_1 @ X28 @ X27)
% 0.52/0.73          | ~ (v1_relat_1 @ X28))),
% 0.52/0.73      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.73        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(cc2_relat_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ A ) =>
% 0.52/0.73       ( ![B:$i]:
% 0.52/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.52/0.73          | (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ 
% 0.52/0.73           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.52/0.73        | (v1_relat_1 @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.73  thf(fc6_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.73  thf('25', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.73  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(cc2_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         ((v4_relat_1 @ X18 @ X19)
% 0.52/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.73  thf('29', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['21', '26', '29'])).
% 0.52/0.73  thf('31', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (((m1_subset_1 @ sk_C @ 
% 0.52/0.73         (k1_zfmisc_1 @ 
% 0.52/0.73          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.52/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.73      inference('sup+', [status(thm)], ['31', '32'])).
% 0.52/0.73  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('35', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('36', plain,
% 0.52/0.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.52/0.73          | (v1_partfun1 @ X24 @ X25)
% 0.52/0.73          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.52/0.73          | ~ (v1_funct_1 @ X24)
% 0.52/0.73          | (v1_xboole_0 @ X26))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.73        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.52/0.73  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('39', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.73      inference('sup+', [status(thm)], ['39', '40'])).
% 0.52/0.73  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('43', plain,
% 0.52/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('44', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['37', '38', '43'])).
% 0.52/0.73  thf('45', plain,
% 0.52/0.73      (![X27 : $i, X28 : $i]:
% 0.52/0.73         (~ (v1_partfun1 @ X28 @ X27)
% 0.52/0.73          | ((k1_relat_1 @ X28) = (X27))
% 0.52/0.73          | ~ (v4_relat_1 @ X28 @ X27)
% 0.52/0.73          | ~ (v1_relat_1 @ X28))),
% 0.52/0.73      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.52/0.73  thf('46', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.73        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.52/0.73  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('49', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         ((v4_relat_1 @ X18 @ X19)
% 0.52/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.73  thf('50', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.73  thf('51', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['46', '47', '50'])).
% 0.52/0.73  thf(fc2_struct_0, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.52/0.73       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.52/0.73  thf('52', plain,
% 0.52/0.73      (![X38 : $i]:
% 0.52/0.73         (~ (v1_xboole_0 @ (u1_struct_0 @ X38))
% 0.52/0.73          | ~ (l1_struct_0 @ X38)
% 0.52/0.73          | (v2_struct_0 @ X38))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.52/0.73  thf('53', plain,
% 0.52/0.73      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['51', '52'])).
% 0.52/0.73  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('55', plain,
% 0.52/0.73      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.52/0.73  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('57', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.52/0.73      inference('clc', [status(thm)], ['55', '56'])).
% 0.52/0.73  thf('58', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['30', '57'])).
% 0.52/0.73  thf('59', plain,
% 0.52/0.73      (![X38 : $i]:
% 0.52/0.73         (~ (v1_xboole_0 @ (u1_struct_0 @ X38))
% 0.52/0.73          | ~ (l1_struct_0 @ X38)
% 0.52/0.73          | (v2_struct_0 @ X38))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.52/0.73  thf('60', plain,
% 0.52/0.73      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['58', '59'])).
% 0.52/0.73  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('62', plain,
% 0.52/0.73      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['60', '61'])).
% 0.52/0.73  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('64', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.52/0.73      inference('clc', [status(thm)], ['62', '63'])).
% 0.52/0.73  thf('65', plain,
% 0.52/0.73      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.52/0.73          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.73           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.52/0.73          sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['13', '64'])).
% 0.52/0.73  thf('66', plain,
% 0.52/0.73      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.52/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.73            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.52/0.73           sk_C)
% 0.52/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['0', '65'])).
% 0.52/0.73  thf('67', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('68', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('69', plain,
% 0.52/0.73      (((m1_subset_1 @ sk_C @ 
% 0.52/0.73         (k1_zfmisc_1 @ 
% 0.52/0.73          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.52/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup+', [status(thm)], ['67', '68'])).
% 0.52/0.73  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('71', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.52/0.73      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.73  thf(d4_tops_2, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.73       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.52/0.73         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.52/0.73  thf('72', plain,
% 0.52/0.73      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.52/0.73         (((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 0.52/0.73          | ~ (v2_funct_1 @ X41)
% 0.52/0.73          | ((k2_tops_2 @ X40 @ X39 @ X41) = (k2_funct_1 @ X41))
% 0.52/0.73          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.52/0.73          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 0.52/0.73          | ~ (v1_funct_1 @ X41))),
% 0.52/0.73      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.52/0.73  thf('73', plain,
% 0.52/0.73      ((~ (v1_funct_1 @ sk_C)
% 0.52/0.73        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.52/0.73        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73            = (k2_funct_1 @ sk_C))
% 0.52/0.73        | ~ (v2_funct_1 @ sk_C)
% 0.52/0.73        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73            != (k2_struct_0 @ sk_B)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['71', '72'])).
% 0.52/0.73  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('75', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('76', plain,
% 0.52/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('77', plain,
% 0.52/0.73      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.52/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup+', [status(thm)], ['75', '76'])).
% 0.52/0.73  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('79', plain,
% 0.52/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['77', '78'])).
% 0.52/0.73  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('81', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('82', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('83', plain,
% 0.52/0.73      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73         = (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('84', plain,
% 0.52/0.73      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73          = (k2_struct_0 @ sk_B))
% 0.52/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.73      inference('sup+', [status(thm)], ['82', '83'])).
% 0.52/0.73  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('86', plain,
% 0.52/0.73      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73         = (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['84', '85'])).
% 0.52/0.73  thf('87', plain,
% 0.52/0.73      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73          = (k2_struct_0 @ sk_B))
% 0.52/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup+', [status(thm)], ['81', '86'])).
% 0.52/0.73  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('89', plain,
% 0.52/0.73      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73         = (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.73  thf('90', plain,
% 0.52/0.73      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73          = (k2_funct_1 @ sk_C))
% 0.52/0.73        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.52/0.73      inference('demod', [status(thm)], ['73', '74', '79', '80', '89'])).
% 0.52/0.73  thf('91', plain,
% 0.52/0.73      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73         = (k2_funct_1 @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['90'])).
% 0.52/0.73  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('93', plain,
% 0.52/0.73      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.52/0.73          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.73           (k2_funct_1 @ sk_C)) @ 
% 0.52/0.73          sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['66', '91', '92'])).
% 0.52/0.73  thf(fc6_funct_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.52/0.73       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.52/0.73         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.52/0.73         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.52/0.73  thf('94', plain,
% 0.52/0.73      (![X10 : $i]:
% 0.52/0.73         ((v2_funct_1 @ (k2_funct_1 @ X10))
% 0.52/0.73          | ~ (v2_funct_1 @ X10)
% 0.52/0.73          | ~ (v1_funct_1 @ X10)
% 0.52/0.73          | ~ (v1_relat_1 @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.52/0.73  thf('95', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('96', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf(t31_funct_2, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.73       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.52/0.73         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.52/0.73           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.52/0.73           ( m1_subset_1 @
% 0.52/0.73             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.52/0.73  thf('97', plain,
% 0.52/0.73      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X33)
% 0.52/0.73          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 0.52/0.73          | (m1_subset_1 @ (k2_funct_1 @ X33) @ 
% 0.52/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.52/0.73          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.52/0.73          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 0.52/0.73          | ~ (v1_funct_1 @ X33))),
% 0.52/0.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.52/0.73  thf('98', plain,
% 0.52/0.73      ((~ (v1_funct_1 @ sk_C)
% 0.52/0.73        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.73           (k1_zfmisc_1 @ 
% 0.52/0.73            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.52/0.73        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73            != (u1_struct_0 @ sk_B))
% 0.52/0.73        | ~ (v2_funct_1 @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['96', '97'])).
% 0.52/0.73  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('100', plain,
% 0.52/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('101', plain,
% 0.52/0.73      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73         = (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['84', '85'])).
% 0.52/0.73  thf('102', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('103', plain,
% 0.52/0.73      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.73         (k1_zfmisc_1 @ 
% 0.52/0.73          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.52/0.73        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.52/0.73      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.52/0.73  thf('104', plain,
% 0.52/0.73      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.52/0.73        | ~ (l1_struct_0 @ sk_B)
% 0.52/0.73        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.73           (k1_zfmisc_1 @ 
% 0.52/0.73            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['95', '103'])).
% 0.52/0.73  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('106', plain,
% 0.52/0.73      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.52/0.73        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.73           (k1_zfmisc_1 @ 
% 0.52/0.73            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.52/0.73      inference('demod', [status(thm)], ['104', '105'])).
% 0.52/0.73  thf('107', plain,
% 0.52/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.52/0.73      inference('simplify', [status(thm)], ['106'])).
% 0.52/0.73  thf('108', plain,
% 0.52/0.73      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.52/0.73         (((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 0.52/0.73          | ~ (v2_funct_1 @ X41)
% 0.52/0.73          | ((k2_tops_2 @ X40 @ X39 @ X41) = (k2_funct_1 @ X41))
% 0.52/0.73          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.52/0.73          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 0.52/0.73          | ~ (v1_funct_1 @ X41))),
% 0.52/0.73      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.52/0.73  thf('109', plain,
% 0.52/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.52/0.73             (k2_struct_0 @ sk_A))
% 0.52/0.73        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.73            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.73        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.73        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.73            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['107', '108'])).
% 0.52/0.73  thf('110', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.52/0.73      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.73  thf('111', plain,
% 0.52/0.73      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X33)
% 0.52/0.73          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 0.52/0.73          | (v1_funct_1 @ (k2_funct_1 @ X33))
% 0.52/0.73          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.52/0.73          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 0.52/0.73          | ~ (v1_funct_1 @ X33))),
% 0.52/0.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.52/0.73  thf('112', plain,
% 0.52/0.73      ((~ (v1_funct_1 @ sk_C)
% 0.52/0.73        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.52/0.73        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.73        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73            != (k2_struct_0 @ sk_B))
% 0.52/0.73        | ~ (v2_funct_1 @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['110', '111'])).
% 0.52/0.73  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('114', plain,
% 0.52/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['77', '78'])).
% 0.52/0.73  thf('115', plain,
% 0.52/0.73      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73         = (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.73  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('117', plain,
% 0.52/0.73      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.73        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.52/0.73      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.52/0.73  thf('118', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['117'])).
% 0.52/0.73  thf('119', plain,
% 0.52/0.73      (![X37 : $i]:
% 0.52/0.73         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.73  thf('120', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('121', plain,
% 0.52/0.73      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X33)
% 0.52/0.73          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 0.52/0.73          | (v1_funct_2 @ (k2_funct_1 @ X33) @ X34 @ X35)
% 0.52/0.73          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.52/0.73          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 0.52/0.73          | ~ (v1_funct_1 @ X33))),
% 0.52/0.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.52/0.73  thf('122', plain,
% 0.52/0.73      ((~ (v1_funct_1 @ sk_C)
% 0.52/0.73        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.52/0.73           (k2_struct_0 @ sk_A))
% 0.52/0.73        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73            != (u1_struct_0 @ sk_B))
% 0.52/0.73        | ~ (v2_funct_1 @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['120', '121'])).
% 0.52/0.73  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('124', plain,
% 0.52/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('125', plain,
% 0.52/0.73      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73         = (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['84', '85'])).
% 0.52/0.73  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('127', plain,
% 0.52/0.73      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.52/0.73         (k2_struct_0 @ sk_A))
% 0.52/0.73        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.52/0.73      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.52/0.73  thf('128', plain,
% 0.52/0.73      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.52/0.73        | ~ (l1_struct_0 @ sk_B)
% 0.52/0.73        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.52/0.73           (k2_struct_0 @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['119', '127'])).
% 0.52/0.73  thf('129', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('130', plain,
% 0.52/0.73      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.52/0.73        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.52/0.73           (k2_struct_0 @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['128', '129'])).
% 0.52/0.73  thf('131', plain,
% 0.52/0.73      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.52/0.73        (k2_struct_0 @ sk_A))),
% 0.52/0.73      inference('simplify', [status(thm)], ['130'])).
% 0.52/0.73  thf('132', plain,
% 0.52/0.73      (![X10 : $i]:
% 0.52/0.73         ((v2_funct_1 @ (k2_funct_1 @ X10))
% 0.52/0.73          | ~ (v2_funct_1 @ X10)
% 0.52/0.73          | ~ (v1_funct_1 @ X10)
% 0.52/0.73          | ~ (v1_relat_1 @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.52/0.73  thf('133', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ 
% 0.52/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.73  thf('134', plain,
% 0.52/0.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.73         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.52/0.73          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.73  thf('135', plain,
% 0.52/0.73      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73         = (k2_relat_1 @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['133', '134'])).
% 0.52/0.73  thf('136', plain,
% 0.52/0.73      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.73         = (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('137', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup+', [status(thm)], ['135', '136'])).
% 0.52/0.73  thf(t155_funct_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.52/0.73       ( ( v2_funct_1 @ B ) =>
% 0.52/0.73         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.52/0.73  thf('138', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X13)
% 0.52/0.73          | ((k10_relat_1 @ X13 @ X14)
% 0.52/0.73              = (k9_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 0.52/0.73          | ~ (v1_funct_1 @ X13)
% 0.52/0.73          | ~ (v1_relat_1 @ X13))),
% 0.52/0.73      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.52/0.73  thf(dt_k2_funct_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.73       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.52/0.73         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.52/0.73  thf('139', plain,
% 0.52/0.73      (![X9 : $i]:
% 0.52/0.73         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.52/0.73          | ~ (v1_funct_1 @ X9)
% 0.52/0.73          | ~ (v1_relat_1 @ X9))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.73  thf('140', plain,
% 0.52/0.73      (![X9 : $i]:
% 0.52/0.73         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.52/0.73          | ~ (v1_funct_1 @ X9)
% 0.52/0.73          | ~ (v1_relat_1 @ X9))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.73  thf(t3_funct_2, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.73       ( ( v1_funct_1 @ A ) & 
% 0.52/0.73         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.52/0.73         ( m1_subset_1 @
% 0.52/0.73           A @ 
% 0.52/0.73           ( k1_zfmisc_1 @
% 0.52/0.73             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.52/0.73  thf('141', plain,
% 0.52/0.73      (![X36 : $i]:
% 0.52/0.73         ((m1_subset_1 @ X36 @ 
% 0.52/0.73           (k1_zfmisc_1 @ 
% 0.52/0.73            (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))))
% 0.52/0.73          | ~ (v1_funct_1 @ X36)
% 0.52/0.73          | ~ (v1_relat_1 @ X36))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.52/0.73  thf('142', plain,
% 0.52/0.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.73         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.52/0.73          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.73  thf('143', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.52/0.73              = (k2_relat_1 @ X0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['141', '142'])).
% 0.52/0.73  thf('144', plain,
% 0.52/0.73      (![X36 : $i]:
% 0.52/0.73         ((v1_funct_2 @ X36 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))
% 0.52/0.73          | ~ (v1_funct_1 @ X36)
% 0.52/0.73          | ~ (v1_relat_1 @ X36))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.52/0.73  thf('145', plain,
% 0.52/0.73      (![X36 : $i]:
% 0.52/0.73         ((m1_subset_1 @ X36 @ 
% 0.52/0.73           (k1_zfmisc_1 @ 
% 0.52/0.73            (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))))
% 0.52/0.73          | ~ (v1_funct_1 @ X36)
% 0.52/0.73          | ~ (v1_relat_1 @ X36))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.52/0.73  thf('146', plain,
% 0.52/0.73      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X33)
% 0.52/0.73          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 0.52/0.73          | (m1_subset_1 @ (k2_funct_1 @ X33) @ 
% 0.52/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.52/0.73          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.52/0.73          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 0.52/0.73          | ~ (v1_funct_1 @ X33))),
% 0.52/0.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.52/0.73  thf('147', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.73          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.52/0.73             (k1_zfmisc_1 @ 
% 0.52/0.73              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.52/0.73          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.52/0.73              != (k2_relat_1 @ X0))
% 0.52/0.73          | ~ (v2_funct_1 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['145', '146'])).
% 0.52/0.73  thf('148', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X0)
% 0.52/0.73          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.52/0.73              != (k2_relat_1 @ X0))
% 0.52/0.73          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.52/0.73             (k1_zfmisc_1 @ 
% 0.52/0.73              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.52/0.73          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['147'])).
% 0.52/0.73  thf('149', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.52/0.73             (k1_zfmisc_1 @ 
% 0.52/0.73              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.52/0.73          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.52/0.73              != (k2_relat_1 @ X0))
% 0.52/0.73          | ~ (v2_funct_1 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['144', '148'])).
% 0.52/0.73  thf('150', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X0)
% 0.52/0.73          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.52/0.73              != (k2_relat_1 @ X0))
% 0.52/0.73          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.52/0.73             (k1_zfmisc_1 @ 
% 0.52/0.73              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['149'])).
% 0.52/0.73  thf('151', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.52/0.73             (k1_zfmisc_1 @ 
% 0.52/0.73              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.52/0.73          | ~ (v2_funct_1 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['143', '150'])).
% 0.52/0.73  thf('152', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X0)
% 0.52/0.73          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.52/0.73             (k1_zfmisc_1 @ 
% 0.52/0.73              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['151'])).
% 0.52/0.73  thf('153', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         ((v4_relat_1 @ X18 @ X19)
% 0.52/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.73  thf('154', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v2_funct_1 @ X0)
% 0.52/0.73          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['152', '153'])).
% 0.52/0.73  thf(t209_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.73       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.52/0.73  thf('155', plain,
% 0.52/0.73      (![X7 : $i, X8 : $i]:
% 0.52/0.73         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.52/0.73          | ~ (v4_relat_1 @ X7 @ X8)
% 0.52/0.73          | ~ (v1_relat_1 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.73  thf('156', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.73          | ((k2_funct_1 @ X0)
% 0.52/0.73              = (k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['154', '155'])).
% 0.52/0.73  thf('157', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ((k2_funct_1 @ X0)
% 0.52/0.73              = (k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v2_funct_1 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['140', '156'])).
% 0.52/0.73  thf('158', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X0)
% 0.52/0.73          | ((k2_funct_1 @ X0)
% 0.52/0.73              = (k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['157'])).
% 0.52/0.73  thf(t148_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ B ) =>
% 0.52/0.73       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.52/0.73  thf('159', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i]:
% 0.52/0.73         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.52/0.73          | ~ (v1_relat_1 @ X4))),
% 0.52/0.73      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.52/0.73  thf('160', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (((k2_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.73            = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v2_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['158', '159'])).
% 0.52/0.73  thf('161', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v2_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.73              = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['139', '160'])).
% 0.52/0.73  thf('162', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (((k2_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.73            = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.52/0.73          | ~ (v2_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['161'])).
% 0.52/0.73  thf('163', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (((k2_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.73            = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v2_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v2_funct_1 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['138', '162'])).
% 0.52/0.73  thf('164', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (v2_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.73              = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.52/0.73      inference('simplify', [status(thm)], ['163'])).
% 0.52/0.73  thf('165', plain,
% 0.52/0.73      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.74          = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.52/0.74      inference('sup+', [status(thm)], ['137', '164'])).
% 0.52/0.74  thf('166', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.52/0.74      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.74  thf('167', plain,
% 0.52/0.74      (![X7 : $i, X8 : $i]:
% 0.52/0.74         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.52/0.74          | ~ (v4_relat_1 @ X7 @ X8)
% 0.52/0.74          | ~ (v1_relat_1 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.74  thf('168', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.52/0.74        | ((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['166', '167'])).
% 0.52/0.74  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('170', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['168', '169'])).
% 0.52/0.74  thf('171', plain,
% 0.52/0.74      (![X4 : $i, X5 : $i]:
% 0.52/0.74         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.52/0.74          | ~ (v1_relat_1 @ X4))),
% 0.52/0.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.52/0.74  thf(t169_relat_1, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ A ) =>
% 0.52/0.74       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.52/0.74  thf('172', plain,
% 0.52/0.74      (![X6 : $i]:
% 0.52/0.74         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.52/0.74          | ~ (v1_relat_1 @ X6))),
% 0.52/0.74      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.52/0.74  thf('173', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.52/0.74            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.52/0.74          | ~ (v1_relat_1 @ X1)
% 0.52/0.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['171', '172'])).
% 0.52/0.74  thf('174', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.52/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.74        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) @ 
% 0.52/0.74            (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.52/0.74            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['170', '173'])).
% 0.52/0.74  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('177', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['168', '169'])).
% 0.52/0.74  thf('178', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['168', '169'])).
% 0.52/0.74  thf('179', plain,
% 0.52/0.74      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.52/0.74         = (k1_relat_1 @ sk_C))),
% 0.52/0.74      inference('demod', [status(thm)], ['174', '175', '176', '177', '178'])).
% 0.52/0.74  thf('180', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['168', '169'])).
% 0.52/0.74  thf('181', plain,
% 0.52/0.74      (![X4 : $i, X5 : $i]:
% 0.52/0.74         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.52/0.74          | ~ (v1_relat_1 @ X4))),
% 0.52/0.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.52/0.74  thf('182', plain,
% 0.52/0.74      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.52/0.74      inference('sup+', [status(thm)], ['180', '181'])).
% 0.52/0.74  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('184', plain,
% 0.52/0.74      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['182', '183'])).
% 0.52/0.74  thf('185', plain,
% 0.52/0.74      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.52/0.74      inference('demod', [status(thm)], ['179', '184'])).
% 0.52/0.74  thf('186', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.52/0.74      inference('sup+', [status(thm)], ['135', '136'])).
% 0.52/0.74  thf('187', plain,
% 0.52/0.74      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.52/0.74      inference('demod', [status(thm)], ['185', '186'])).
% 0.52/0.74  thf('188', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.52/0.74      inference('clc', [status(thm)], ['55', '56'])).
% 0.52/0.74  thf('189', plain,
% 0.52/0.74      (((k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)) = (k2_struct_0 @ sk_A))),
% 0.52/0.74      inference('demod', [status(thm)], ['187', '188'])).
% 0.52/0.74  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('193', plain,
% 0.52/0.74      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.52/0.74      inference('demod', [status(thm)], ['165', '189', '190', '191', '192'])).
% 0.52/0.74  thf(t61_funct_1, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.74       ( ( v2_funct_1 @ A ) =>
% 0.52/0.74         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.52/0.74             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.52/0.74           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.52/0.74             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.52/0.74  thf('194', plain,
% 0.52/0.74      (![X15 : $i]:
% 0.52/0.74         (~ (v2_funct_1 @ X15)
% 0.52/0.74          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15))
% 0.52/0.74              = (k6_relat_1 @ (k1_relat_1 @ X15)))
% 0.52/0.74          | ~ (v1_funct_1 @ X15)
% 0.52/0.74          | ~ (v1_relat_1 @ X15))),
% 0.52/0.74      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.52/0.74  thf(t64_funct_1, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.74       ( ![B:$i]:
% 0.52/0.74         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.52/0.74           ( ( ( v2_funct_1 @ A ) & 
% 0.52/0.74               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.52/0.74               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.52/0.74             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.52/0.74  thf('195', plain,
% 0.52/0.74      (![X16 : $i, X17 : $i]:
% 0.52/0.74         (~ (v1_relat_1 @ X16)
% 0.52/0.74          | ~ (v1_funct_1 @ X16)
% 0.52/0.74          | ((X16) = (k2_funct_1 @ X17))
% 0.52/0.74          | ((k5_relat_1 @ X16 @ X17) != (k6_relat_1 @ (k2_relat_1 @ X17)))
% 0.52/0.74          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 0.52/0.74          | ~ (v2_funct_1 @ X17)
% 0.52/0.74          | ~ (v1_funct_1 @ X17)
% 0.52/0.74          | ~ (v1_relat_1 @ X17))),
% 0.52/0.74      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.52/0.74  thf('196', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.52/0.74            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.52/0.74          | ~ (v1_relat_1 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | ~ (v2_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.52/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.52/0.74          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.52/0.74          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_relat_1 @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['194', '195'])).
% 0.52/0.74  thf('197', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.52/0.74          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.52/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.52/0.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.52/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.74          | ~ (v2_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_relat_1 @ X0)
% 0.52/0.74          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.52/0.74              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['196'])).
% 0.52/0.74  thf('198', plain,
% 0.52/0.74      ((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 0.52/0.74          != (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.52/0.74        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.74        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.74        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.74        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['193', '197'])).
% 0.52/0.74  thf('199', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.52/0.74      inference('clc', [status(thm)], ['55', '56'])).
% 0.52/0.74  thf('200', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('202', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('203', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_C @ 
% 0.52/0.74        (k1_zfmisc_1 @ 
% 0.52/0.74         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.52/0.74      inference('demod', [status(thm)], ['69', '70'])).
% 0.52/0.74  thf('204', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.74         (~ (v2_funct_1 @ X33)
% 0.52/0.74          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 0.52/0.74          | (m1_subset_1 @ (k2_funct_1 @ X33) @ 
% 0.52/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.52/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.52/0.74          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 0.52/0.74          | ~ (v1_funct_1 @ X33))),
% 0.52/0.74      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.52/0.74  thf('205', plain,
% 0.52/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.52/0.74        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.52/0.74        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.74           (k1_zfmisc_1 @ 
% 0.52/0.74            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.52/0.74        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.74            != (k2_struct_0 @ sk_B))
% 0.52/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.52/0.74      inference('sup-', [status(thm)], ['203', '204'])).
% 0.52/0.74  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('207', plain,
% 0.52/0.74      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.52/0.74      inference('demod', [status(thm)], ['77', '78'])).
% 0.52/0.74  thf('208', plain,
% 0.52/0.74      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.74         = (k2_struct_0 @ sk_B))),
% 0.52/0.74      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.74  thf('209', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('210', plain,
% 0.52/0.74      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.74         (k1_zfmisc_1 @ 
% 0.52/0.74          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.52/0.74        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.52/0.74      inference('demod', [status(thm)], ['205', '206', '207', '208', '209'])).
% 0.52/0.74  thf('211', plain,
% 0.52/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.74        (k1_zfmisc_1 @ 
% 0.52/0.74         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['210'])).
% 0.52/0.74  thf('212', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.52/0.74          | (v1_relat_1 @ X0)
% 0.52/0.74          | ~ (v1_relat_1 @ X1))),
% 0.52/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.74  thf('213', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ 
% 0.52/0.74           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 0.52/0.74        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['211', '212'])).
% 0.52/0.74  thf('214', plain,
% 0.52/0.74      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.52/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.74  thf('215', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.52/0.74      inference('demod', [status(thm)], ['213', '214'])).
% 0.52/0.74  thf('216', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.52/0.74      inference('simplify', [status(thm)], ['117'])).
% 0.52/0.74  thf('217', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.52/0.74      inference('sup+', [status(thm)], ['135', '136'])).
% 0.52/0.74  thf('218', plain,
% 0.52/0.74      ((((k6_relat_1 @ (k2_struct_0 @ sk_A))
% 0.52/0.74          != (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.52/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.74        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.74        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.52/0.74      inference('demod', [status(thm)],
% 0.52/0.74                ['198', '199', '200', '201', '202', '215', '216', '217'])).
% 0.52/0.74  thf('219', plain,
% 0.52/0.74      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.74        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['218'])).
% 0.52/0.74  thf('220', plain,
% 0.52/0.74      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.52/0.74      inference('demod', [status(thm)], ['165', '189', '190', '191', '192'])).
% 0.52/0.74  thf('221', plain,
% 0.52/0.74      (![X9 : $i]:
% 0.52/0.74         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.52/0.74          | ~ (v1_funct_1 @ X9)
% 0.52/0.74          | ~ (v1_relat_1 @ X9))),
% 0.52/0.74      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.74  thf(t154_funct_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.52/0.74       ( ( v2_funct_1 @ B ) =>
% 0.52/0.74         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.52/0.74  thf('222', plain,
% 0.52/0.74      (![X11 : $i, X12 : $i]:
% 0.52/0.74         (~ (v2_funct_1 @ X11)
% 0.52/0.74          | ((k9_relat_1 @ X11 @ X12)
% 0.52/0.74              = (k10_relat_1 @ (k2_funct_1 @ X11) @ X12))
% 0.52/0.74          | ~ (v1_funct_1 @ X11)
% 0.52/0.74          | ~ (v1_relat_1 @ X11))),
% 0.52/0.74      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.52/0.74  thf('223', plain,
% 0.52/0.74      (![X6 : $i]:
% 0.52/0.74         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.52/0.74          | ~ (v1_relat_1 @ X6))),
% 0.52/0.74      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.52/0.74  thf('224', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.52/0.74            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.52/0.74          | ~ (v1_relat_1 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | ~ (v2_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['222', '223'])).
% 0.52/0.74  thf('225', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (v1_relat_1 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | ~ (v2_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_relat_1 @ X0)
% 0.52/0.74          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.52/0.74              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['221', '224'])).
% 0.52/0.74  thf('226', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.52/0.74            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.52/0.74          | ~ (v2_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_relat_1 @ X0))),
% 0.52/0.74      inference('simplify', [status(thm)], ['225'])).
% 0.52/0.74  thf('227', plain,
% 0.52/0.74      ((((k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.52/0.74          = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.52/0.74      inference('sup+', [status(thm)], ['220', '226'])).
% 0.52/0.74  thf('228', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.52/0.74      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.74  thf('229', plain,
% 0.52/0.74      (![X7 : $i, X8 : $i]:
% 0.52/0.74         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.52/0.74          | ~ (v4_relat_1 @ X7 @ X8)
% 0.52/0.74          | ~ (v1_relat_1 @ X7))),
% 0.52/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.74  thf('230', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.52/0.74        | ((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['228', '229'])).
% 0.52/0.74  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('232', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['230', '231'])).
% 0.52/0.74  thf('233', plain,
% 0.52/0.74      (![X4 : $i, X5 : $i]:
% 0.52/0.74         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.52/0.74          | ~ (v1_relat_1 @ X4))),
% 0.52/0.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.52/0.74  thf('234', plain,
% 0.52/0.74      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.52/0.74      inference('sup+', [status(thm)], ['232', '233'])).
% 0.52/0.74  thf('235', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('236', plain,
% 0.52/0.74      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['234', '235'])).
% 0.52/0.74  thf('237', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.52/0.74      inference('sup+', [status(thm)], ['135', '136'])).
% 0.52/0.74  thf('238', plain,
% 0.52/0.74      (((k2_struct_0 @ sk_B) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['236', '237'])).
% 0.52/0.74  thf('239', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('240', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('241', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('242', plain,
% 0.52/0.74      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.74      inference('demod', [status(thm)], ['227', '238', '239', '240', '241'])).
% 0.52/0.74  thf('243', plain,
% 0.52/0.74      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.74        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.52/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.74      inference('demod', [status(thm)], ['219', '242'])).
% 0.52/0.74  thf('244', plain,
% 0.52/0.74      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.74        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['243'])).
% 0.52/0.74  thf('245', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.52/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.52/0.74        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['132', '244'])).
% 0.52/0.74  thf('246', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('247', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('248', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('249', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.74      inference('demod', [status(thm)], ['245', '246', '247', '248'])).
% 0.52/0.74  thf('250', plain,
% 0.52/0.74      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.74          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.52/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.74        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.74            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['109', '118', '131', '249'])).
% 0.52/0.74  thf('251', plain,
% 0.52/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.52/0.74        (k1_zfmisc_1 @ 
% 0.52/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['106'])).
% 0.52/0.74  thf('252', plain,
% 0.52/0.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.74         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.52/0.74          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.52/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.74  thf('253', plain,
% 0.52/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.74         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['251', '252'])).
% 0.52/0.74  thf('254', plain,
% 0.52/0.74      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.52/0.74      inference('demod', [status(thm)], ['165', '189', '190', '191', '192'])).
% 0.52/0.74  thf('255', plain,
% 0.52/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.74         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.52/0.74      inference('demod', [status(thm)], ['253', '254'])).
% 0.52/0.74  thf('256', plain,
% 0.52/0.74      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.74          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.52/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.74        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['250', '255'])).
% 0.52/0.74  thf('257', plain,
% 0.52/0.74      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.74        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.74            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['256'])).
% 0.52/0.74  thf('258', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.52/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.52/0.74        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.74            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['94', '257'])).
% 0.52/0.74  thf('259', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.74  thf('260', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('261', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('262', plain,
% 0.52/0.74      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.74         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.52/0.74      inference('demod', [status(thm)], ['258', '259', '260', '261'])).
% 0.52/0.74  thf('263', plain,
% 0.52/0.74      (![X37 : $i]:
% 0.52/0.74         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.52/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.74  thf('264', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_C @ 
% 0.52/0.74        (k1_zfmisc_1 @ 
% 0.52/0.74         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.74  thf('265', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_C @ 
% 0.52/0.74        (k1_zfmisc_1 @ 
% 0.52/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(reflexivity_r2_funct_2, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.74         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.74       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.52/0.74  thf('266', plain,
% 0.52/0.74      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.74         ((r2_funct_2 @ X29 @ X30 @ X31 @ X31)
% 0.52/0.74          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.52/0.74          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.52/0.74          | ~ (v1_funct_1 @ X31)
% 0.52/0.74          | ~ (v1_funct_1 @ X32)
% 0.52/0.74          | ~ (v1_funct_2 @ X32 @ X29 @ X30)
% 0.52/0.74          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.52/0.74      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.52/0.74  thf('267', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X0 @ 
% 0.52/0.74             (k1_zfmisc_1 @ 
% 0.52/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.52/0.74          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.52/0.74          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.74          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.74             sk_C))),
% 0.52/0.74      inference('sup-', [status(thm)], ['265', '266'])).
% 0.52/0.74  thf('268', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('269', plain,
% 0.52/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('270', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X0 @ 
% 0.52/0.74             (k1_zfmisc_1 @ 
% 0.52/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.52/0.74          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.74             sk_C))),
% 0.52/0.74      inference('demod', [status(thm)], ['267', '268', '269'])).
% 0.52/0.74  thf('271', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.52/0.74      inference('clc', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('272', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.52/0.74      inference('clc', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('273', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.52/0.74      inference('clc', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('274', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X0 @ 
% 0.52/0.74             (k1_zfmisc_1 @ 
% 0.52/0.74              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.52/0.74          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.74             sk_C))),
% 0.52/0.74      inference('demod', [status(thm)], ['270', '271', '272', '273'])).
% 0.52/0.74  thf('275', plain,
% 0.52/0.74      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.52/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.74        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['264', '274'])).
% 0.52/0.74  thf('276', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('277', plain,
% 0.52/0.74      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.74      inference('demod', [status(thm)], ['41', '42'])).
% 0.52/0.74  thf('278', plain,
% 0.52/0.74      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['275', '276', '277'])).
% 0.52/0.74  thf('279', plain,
% 0.52/0.74      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.52/0.74        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.74      inference('sup+', [status(thm)], ['263', '278'])).
% 0.52/0.74  thf('280', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('281', plain,
% 0.52/0.74      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.52/0.74      inference('demod', [status(thm)], ['279', '280'])).
% 0.52/0.74  thf('282', plain, ($false),
% 0.52/0.74      inference('demod', [status(thm)], ['93', '262', '281'])).
% 0.52/0.74  
% 0.52/0.74  % SZS output end Refutation
% 0.52/0.74  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
