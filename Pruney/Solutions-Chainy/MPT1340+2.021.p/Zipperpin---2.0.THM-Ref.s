%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vwt7MBFTlS

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:09 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 656 expanded)
%              Number of leaves         :   40 ( 206 expanded)
%              Depth                    :   23
%              Number of atoms          : 1770 (15341 expanded)
%              Number of equality atoms :  103 ( 495 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('11',plain,(
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

thf('12',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X20 @ X18 )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','26'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_partfun1 @ X13 @ X12 )
      | ( ( k1_relat_1 @ X13 )
        = X12 )
      | ~ ( v4_relat_1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('29',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','32','35'])).

thf('37',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('42',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('44',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

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

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('52',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('68',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53','60','68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

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

thf('73',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('75',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('79',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('84',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('88',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','82','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('94',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('95',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['41','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','109'])).

thf('111',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('123',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('125',plain,(
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

thf('126',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('131',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['126','127','128','129','130'])).

thf('132',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['123','132'])).

thf('134',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','133'])).

thf('135',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('137',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_funct_2 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('138',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_funct_2 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['136','138'])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','142','143','144','145'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('147',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['10','146','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vwt7MBFTlS
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.25/1.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.25/1.45  % Solved by: fo/fo7.sh
% 1.25/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.25/1.45  % done 1729 iterations in 0.992s
% 1.25/1.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.25/1.45  % SZS output start Refutation
% 1.25/1.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.25/1.45  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.25/1.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.25/1.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.25/1.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.25/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.25/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.25/1.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.25/1.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.25/1.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.25/1.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.25/1.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.25/1.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.25/1.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.25/1.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.25/1.45  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.25/1.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.25/1.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.25/1.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.25/1.45  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.25/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.25/1.45  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.25/1.45  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.25/1.45  thf(sk_C_type, type, sk_C: $i).
% 1.25/1.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.25/1.45  thf(t64_tops_2, conjecture,
% 1.25/1.45    (![A:$i]:
% 1.25/1.45     ( ( l1_struct_0 @ A ) =>
% 1.25/1.45       ( ![B:$i]:
% 1.25/1.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.25/1.45           ( ![C:$i]:
% 1.25/1.45             ( ( ( v1_funct_1 @ C ) & 
% 1.25/1.45                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.25/1.45                 ( m1_subset_1 @
% 1.25/1.45                   C @ 
% 1.25/1.45                   ( k1_zfmisc_1 @
% 1.25/1.45                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.25/1.45               ( ( ( ( k2_relset_1 @
% 1.25/1.45                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.25/1.45                     ( k2_struct_0 @ B ) ) & 
% 1.25/1.45                   ( v2_funct_1 @ C ) ) =>
% 1.25/1.45                 ( r2_funct_2 @
% 1.25/1.45                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.25/1.45                   ( k2_tops_2 @
% 1.25/1.45                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.25/1.45                     ( k2_tops_2 @
% 1.25/1.45                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 1.25/1.45                   C ) ) ) ) ) ) ))).
% 1.25/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.25/1.45    (~( ![A:$i]:
% 1.25/1.45        ( ( l1_struct_0 @ A ) =>
% 1.25/1.45          ( ![B:$i]:
% 1.25/1.45            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.25/1.45              ( ![C:$i]:
% 1.25/1.45                ( ( ( v1_funct_1 @ C ) & 
% 1.25/1.45                    ( v1_funct_2 @
% 1.25/1.45                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.25/1.45                    ( m1_subset_1 @
% 1.25/1.45                      C @ 
% 1.25/1.45                      ( k1_zfmisc_1 @
% 1.25/1.45                        ( k2_zfmisc_1 @
% 1.25/1.45                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.25/1.45                  ( ( ( ( k2_relset_1 @
% 1.25/1.45                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.25/1.45                        ( k2_struct_0 @ B ) ) & 
% 1.25/1.45                      ( v2_funct_1 @ C ) ) =>
% 1.25/1.45                    ( r2_funct_2 @
% 1.25/1.45                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.25/1.45                      ( k2_tops_2 @
% 1.25/1.45                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.25/1.45                        ( k2_tops_2 @
% 1.25/1.45                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 1.25/1.45                      C ) ) ) ) ) ) ) )),
% 1.25/1.45    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 1.25/1.45  thf('0', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf(redefinition_k2_relset_1, axiom,
% 1.25/1.45    (![A:$i,B:$i,C:$i]:
% 1.25/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.25/1.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.25/1.45  thf('1', plain,
% 1.25/1.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.25/1.45         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.25/1.45          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.25/1.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.25/1.45  thf('2', plain,
% 1.25/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.25/1.45         = (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('sup-', [status(thm)], ['0', '1'])).
% 1.25/1.45  thf('3', plain,
% 1.25/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.25/1.45         = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.25/1.45  thf(fc5_struct_0, axiom,
% 1.25/1.45    (![A:$i]:
% 1.25/1.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.25/1.45       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.25/1.45  thf('5', plain,
% 1.25/1.45      (![X25 : $i]:
% 1.25/1.45         (~ (v1_xboole_0 @ (k2_struct_0 @ X25))
% 1.25/1.45          | ~ (l1_struct_0 @ X25)
% 1.25/1.45          | (v2_struct_0 @ X25))),
% 1.25/1.45      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.25/1.45  thf('6', plain,
% 1.25/1.45      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.25/1.45        | (v2_struct_0 @ sk_B)
% 1.25/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup-', [status(thm)], ['4', '5'])).
% 1.25/1.45  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('8', plain,
% 1.25/1.45      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.25/1.45      inference('demod', [status(thm)], ['6', '7'])).
% 1.25/1.45  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('clc', [status(thm)], ['8', '9'])).
% 1.25/1.45  thf(t65_funct_1, axiom,
% 1.25/1.45    (![A:$i]:
% 1.25/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.25/1.45       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.25/1.45  thf('11', plain,
% 1.25/1.45      (![X2 : $i]:
% 1.25/1.45         (~ (v2_funct_1 @ X2)
% 1.25/1.45          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 1.25/1.45          | ~ (v1_funct_1 @ X2)
% 1.25/1.45          | ~ (v1_relat_1 @ X2))),
% 1.25/1.45      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.25/1.45  thf(d3_struct_0, axiom,
% 1.25/1.45    (![A:$i]:
% 1.25/1.45     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.25/1.45  thf('12', plain,
% 1.25/1.45      (![X24 : $i]:
% 1.25/1.45         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.25/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.25/1.45  thf('13', plain,
% 1.25/1.45      (![X24 : $i]:
% 1.25/1.45         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.25/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.25/1.45  thf('14', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('15', plain,
% 1.25/1.45      (((m1_subset_1 @ sk_C @ 
% 1.25/1.45         (k1_zfmisc_1 @ 
% 1.25/1.45          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.25/1.45        | ~ (l1_struct_0 @ sk_A))),
% 1.25/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.25/1.45  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('17', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.25/1.45      inference('demod', [status(thm)], ['15', '16'])).
% 1.25/1.45  thf(t132_funct_2, axiom,
% 1.25/1.45    (![A:$i,B:$i,C:$i]:
% 1.25/1.45     ( ( ( v1_funct_1 @ C ) & 
% 1.25/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.45       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.25/1.45           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.25/1.45           ( v1_partfun1 @ C @ A ) ) ) ))).
% 1.25/1.45  thf('18', plain,
% 1.25/1.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.25/1.45         (((X18) = (k1_xboole_0))
% 1.25/1.45          | ~ (v1_funct_1 @ X19)
% 1.25/1.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 1.25/1.45          | (v1_partfun1 @ X19 @ X20)
% 1.25/1.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 1.25/1.45          | ~ (v1_funct_2 @ X19 @ X20 @ X18)
% 1.25/1.45          | ~ (v1_funct_1 @ X19))),
% 1.25/1.45      inference('cnf', [status(esa)], [t132_funct_2])).
% 1.25/1.45  thf('19', plain,
% 1.25/1.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.25/1.45         (~ (v1_funct_2 @ X19 @ X20 @ X18)
% 1.25/1.45          | (v1_partfun1 @ X19 @ X20)
% 1.25/1.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 1.25/1.45          | ~ (v1_funct_1 @ X19)
% 1.25/1.45          | ((X18) = (k1_xboole_0)))),
% 1.25/1.45      inference('simplify', [status(thm)], ['18'])).
% 1.25/1.45  thf('20', plain,
% 1.25/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.25/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.25/1.45        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.25/1.45        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.25/1.45      inference('sup-', [status(thm)], ['17', '19'])).
% 1.25/1.45  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('22', plain,
% 1.25/1.45      (![X24 : $i]:
% 1.25/1.45         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.25/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.25/1.45  thf('23', plain,
% 1.25/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('24', plain,
% 1.25/1.45      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.25/1.45        | ~ (l1_struct_0 @ sk_A))),
% 1.25/1.45      inference('sup+', [status(thm)], ['22', '23'])).
% 1.25/1.45  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('26', plain,
% 1.25/1.45      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.25/1.45      inference('demod', [status(thm)], ['24', '25'])).
% 1.25/1.45  thf('27', plain,
% 1.25/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.25/1.45        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 1.25/1.45      inference('demod', [status(thm)], ['20', '21', '26'])).
% 1.25/1.45  thf(d4_partfun1, axiom,
% 1.25/1.45    (![A:$i,B:$i]:
% 1.25/1.45     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.25/1.45       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.25/1.45  thf('28', plain,
% 1.25/1.45      (![X12 : $i, X13 : $i]:
% 1.25/1.45         (~ (v1_partfun1 @ X13 @ X12)
% 1.25/1.45          | ((k1_relat_1 @ X13) = (X12))
% 1.25/1.45          | ~ (v4_relat_1 @ X13 @ X12)
% 1.25/1.45          | ~ (v1_relat_1 @ X13))),
% 1.25/1.45      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.25/1.45  thf('29', plain,
% 1.25/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.25/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.25/1.45        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.25/1.45        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.25/1.45      inference('sup-', [status(thm)], ['27', '28'])).
% 1.25/1.45  thf('30', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf(cc1_relset_1, axiom,
% 1.25/1.45    (![A:$i,B:$i,C:$i]:
% 1.25/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.25/1.45       ( v1_relat_1 @ C ) ))).
% 1.25/1.45  thf('31', plain,
% 1.25/1.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.25/1.45         ((v1_relat_1 @ X3)
% 1.25/1.45          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.25/1.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.25/1.45  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 1.25/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.25/1.45  thf('33', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.25/1.45      inference('demod', [status(thm)], ['15', '16'])).
% 1.25/1.45  thf(cc2_relset_1, axiom,
% 1.25/1.45    (![A:$i,B:$i,C:$i]:
% 1.25/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.25/1.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.25/1.45  thf('34', plain,
% 1.25/1.45      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.25/1.45         ((v4_relat_1 @ X6 @ X7)
% 1.25/1.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.25/1.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.25/1.45  thf('35', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.25/1.45      inference('sup-', [status(thm)], ['33', '34'])).
% 1.25/1.45  thf('36', plain,
% 1.25/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.25/1.45        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.25/1.45      inference('demod', [status(thm)], ['29', '32', '35'])).
% 1.25/1.45  thf('37', plain,
% 1.25/1.45      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 1.25/1.45        | ~ (l1_struct_0 @ sk_B)
% 1.25/1.45        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.25/1.45      inference('sup+', [status(thm)], ['12', '36'])).
% 1.25/1.45  thf('38', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.25/1.45  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('40', plain,
% 1.25/1.45      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.25/1.45        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.25/1.45      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.25/1.45  thf(t55_funct_1, axiom,
% 1.25/1.45    (![A:$i]:
% 1.25/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.25/1.45       ( ( v2_funct_1 @ A ) =>
% 1.25/1.45         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.25/1.45           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.25/1.45  thf('41', plain,
% 1.25/1.45      (![X1 : $i]:
% 1.25/1.45         (~ (v2_funct_1 @ X1)
% 1.25/1.45          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.25/1.45          | ~ (v1_funct_1 @ X1)
% 1.25/1.45          | ~ (v1_relat_1 @ X1))),
% 1.25/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.25/1.45  thf('42', plain,
% 1.25/1.45      (![X24 : $i]:
% 1.25/1.45         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.25/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.25/1.45  thf(fc6_funct_1, axiom,
% 1.25/1.45    (![A:$i]:
% 1.25/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 1.25/1.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.25/1.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 1.25/1.45         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.25/1.45  thf('43', plain,
% 1.25/1.45      (![X0 : $i]:
% 1.25/1.45         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.25/1.45          | ~ (v2_funct_1 @ X0)
% 1.25/1.45          | ~ (v1_funct_1 @ X0)
% 1.25/1.45          | ~ (v1_relat_1 @ X0))),
% 1.25/1.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.25/1.45  thf('44', plain,
% 1.25/1.45      (![X24 : $i]:
% 1.25/1.45         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.25/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.25/1.45  thf('45', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('46', plain,
% 1.25/1.45      (((m1_subset_1 @ sk_C @ 
% 1.25/1.45         (k1_zfmisc_1 @ 
% 1.25/1.45          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.25/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['44', '45'])).
% 1.25/1.45  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('48', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.25/1.45      inference('demod', [status(thm)], ['46', '47'])).
% 1.25/1.45  thf('49', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.25/1.45  thf('50', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.25/1.45      inference('demod', [status(thm)], ['48', '49'])).
% 1.25/1.45  thf(t31_funct_2, axiom,
% 1.25/1.45    (![A:$i,B:$i,C:$i]:
% 1.25/1.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.25/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.45       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.25/1.45         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.25/1.45           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.25/1.45           ( m1_subset_1 @
% 1.25/1.45             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.25/1.45  thf('51', plain,
% 1.25/1.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.25/1.45         (~ (v2_funct_1 @ X21)
% 1.25/1.45          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 1.25/1.45          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 1.25/1.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.25/1.45          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 1.25/1.45          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 1.25/1.45          | ~ (v1_funct_1 @ X21))),
% 1.25/1.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.25/1.45  thf('52', plain,
% 1.25/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.25/1.45        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.25/1.45        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.25/1.45           (k1_zfmisc_1 @ 
% 1.25/1.45            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 1.25/1.45        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45            != (k2_relat_1 @ sk_C))
% 1.25/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.25/1.45      inference('sup-', [status(thm)], ['50', '51'])).
% 1.25/1.45  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('54', plain,
% 1.25/1.45      (![X24 : $i]:
% 1.25/1.45         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.25/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.25/1.45  thf('55', plain,
% 1.25/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('56', plain,
% 1.25/1.45      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.25/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['54', '55'])).
% 1.25/1.45  thf('57', plain, ((l1_struct_0 @ sk_B)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('58', plain,
% 1.25/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('demod', [status(thm)], ['56', '57'])).
% 1.25/1.45  thf('59', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.25/1.45  thf('60', plain,
% 1.25/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('demod', [status(thm)], ['58', '59'])).
% 1.25/1.45  thf('61', plain,
% 1.25/1.45      (![X24 : $i]:
% 1.25/1.45         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.25/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.25/1.45  thf('62', plain,
% 1.25/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.25/1.45         = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('63', plain,
% 1.25/1.45      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.25/1.45          = (k2_struct_0 @ sk_B))
% 1.25/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['61', '62'])).
% 1.25/1.45  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('65', plain,
% 1.25/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.25/1.45         = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('demod', [status(thm)], ['63', '64'])).
% 1.25/1.45  thf('66', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.25/1.45  thf('67', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.25/1.45  thf('68', plain,
% 1.25/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45         = (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.25/1.45  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('70', plain,
% 1.25/1.45      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.25/1.45         (k1_zfmisc_1 @ 
% 1.25/1.45          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 1.25/1.45        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.25/1.45      inference('demod', [status(thm)], ['52', '53', '60', '68', '69'])).
% 1.25/1.45  thf('71', plain,
% 1.25/1.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 1.25/1.45      inference('simplify', [status(thm)], ['70'])).
% 1.25/1.45  thf(d4_tops_2, axiom,
% 1.25/1.45    (![A:$i,B:$i,C:$i]:
% 1.25/1.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.25/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.45       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.25/1.45         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.25/1.45  thf('72', plain,
% 1.25/1.45      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.25/1.45         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 1.25/1.45          | ~ (v2_funct_1 @ X28)
% 1.25/1.45          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 1.25/1.45          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 1.25/1.45          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 1.25/1.45          | ~ (v1_funct_1 @ X28))),
% 1.25/1.45      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.25/1.45  thf('73', plain,
% 1.25/1.45      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.25/1.45        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.25/1.45             (u1_struct_0 @ sk_A))
% 1.25/1.45        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.25/1.45        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.25/1.45        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 1.25/1.45      inference('sup-', [status(thm)], ['71', '72'])).
% 1.25/1.45  thf('74', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.25/1.45      inference('demod', [status(thm)], ['48', '49'])).
% 1.25/1.45  thf('75', plain,
% 1.25/1.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.25/1.45         (~ (v2_funct_1 @ X21)
% 1.25/1.45          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 1.25/1.45          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 1.25/1.45          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 1.25/1.45          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 1.25/1.45          | ~ (v1_funct_1 @ X21))),
% 1.25/1.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.25/1.45  thf('76', plain,
% 1.25/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.25/1.45        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.25/1.45        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.25/1.45        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45            != (k2_relat_1 @ sk_C))
% 1.25/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.25/1.45      inference('sup-', [status(thm)], ['74', '75'])).
% 1.25/1.45  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('78', plain,
% 1.25/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('demod', [status(thm)], ['58', '59'])).
% 1.25/1.45  thf('79', plain,
% 1.25/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45         = (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.25/1.45  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('81', plain,
% 1.25/1.45      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.25/1.45        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.25/1.45      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 1.25/1.45  thf('82', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.25/1.45      inference('simplify', [status(thm)], ['81'])).
% 1.25/1.45  thf('83', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.25/1.45      inference('demod', [status(thm)], ['48', '49'])).
% 1.25/1.45  thf('84', plain,
% 1.25/1.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.25/1.45         (~ (v2_funct_1 @ X21)
% 1.25/1.45          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 1.25/1.45          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 1.25/1.45          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 1.25/1.45          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 1.25/1.45          | ~ (v1_funct_1 @ X21))),
% 1.25/1.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.25/1.45  thf('85', plain,
% 1.25/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.25/1.45        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.25/1.45        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.25/1.45           (u1_struct_0 @ sk_A))
% 1.25/1.45        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45            != (k2_relat_1 @ sk_C))
% 1.25/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.25/1.45      inference('sup-', [status(thm)], ['83', '84'])).
% 1.25/1.45  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('87', plain,
% 1.25/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('demod', [status(thm)], ['58', '59'])).
% 1.25/1.45  thf('88', plain,
% 1.25/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45         = (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.25/1.45  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('90', plain,
% 1.25/1.45      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.25/1.45         (u1_struct_0 @ sk_A))
% 1.25/1.45        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.25/1.45      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 1.25/1.45  thf('91', plain,
% 1.25/1.45      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.25/1.45        (u1_struct_0 @ sk_A))),
% 1.25/1.45      inference('simplify', [status(thm)], ['90'])).
% 1.25/1.45  thf('92', plain,
% 1.25/1.45      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.25/1.45        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.25/1.45        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 1.25/1.45      inference('demod', [status(thm)], ['73', '82', '91'])).
% 1.25/1.45  thf('93', plain,
% 1.25/1.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 1.25/1.45      inference('simplify', [status(thm)], ['70'])).
% 1.25/1.45  thf('94', plain,
% 1.25/1.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.25/1.45         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.25/1.45          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.25/1.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.25/1.45  thf('95', plain,
% 1.25/1.45      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.25/1.45      inference('sup-', [status(thm)], ['93', '94'])).
% 1.25/1.45  thf('96', plain,
% 1.25/1.45      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.25/1.45        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.25/1.45        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 1.25/1.45      inference('demod', [status(thm)], ['92', '95'])).
% 1.25/1.45  thf('97', plain,
% 1.25/1.45      ((~ (v1_relat_1 @ sk_C)
% 1.25/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.25/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.25/1.45        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 1.25/1.45        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.25/1.45      inference('sup-', [status(thm)], ['43', '96'])).
% 1.25/1.45  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 1.25/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.25/1.45  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('101', plain,
% 1.25/1.45      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 1.25/1.45        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.25/1.45      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 1.25/1.45  thf('102', plain,
% 1.25/1.45      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 1.25/1.45        | ~ (l1_struct_0 @ sk_A)
% 1.25/1.45        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.25/1.45      inference('sup-', [status(thm)], ['42', '101'])).
% 1.25/1.45  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('104', plain,
% 1.25/1.45      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 1.25/1.45        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.25/1.45      inference('demod', [status(thm)], ['102', '103'])).
% 1.25/1.45  thf('105', plain,
% 1.25/1.45      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 1.25/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.25/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.25/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.25/1.45        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.25/1.45      inference('sup-', [status(thm)], ['41', '104'])).
% 1.25/1.45  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 1.25/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.25/1.45  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('109', plain,
% 1.25/1.45      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 1.25/1.45        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.25/1.45      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 1.25/1.45  thf('110', plain,
% 1.25/1.45      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.25/1.45        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.25/1.45        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.25/1.45      inference('sup-', [status(thm)], ['40', '109'])).
% 1.25/1.45  thf('111', plain,
% 1.25/1.45      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.25/1.45        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.25/1.45      inference('simplify', [status(thm)], ['110'])).
% 1.25/1.45  thf('112', plain,
% 1.25/1.45      (![X24 : $i]:
% 1.25/1.45         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.25/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.25/1.45  thf('113', plain,
% 1.25/1.45      (![X24 : $i]:
% 1.25/1.45         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 1.25/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.25/1.45  thf('114', plain,
% 1.25/1.45      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.25/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 1.25/1.45          sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('115', plain,
% 1.25/1.45      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.25/1.45           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 1.25/1.45           sk_C)
% 1.25/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup-', [status(thm)], ['113', '114'])).
% 1.25/1.45  thf('116', plain, ((l1_struct_0 @ sk_B)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('117', plain,
% 1.25/1.45      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.25/1.45          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 1.25/1.45          sk_C)),
% 1.25/1.45      inference('demod', [status(thm)], ['115', '116'])).
% 1.25/1.45  thf('118', plain,
% 1.25/1.45      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.25/1.45           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 1.25/1.45           sk_C)
% 1.25/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup-', [status(thm)], ['112', '117'])).
% 1.25/1.45  thf('119', plain, ((l1_struct_0 @ sk_B)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('120', plain,
% 1.25/1.45      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.25/1.45          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 1.25/1.45          sk_C)),
% 1.25/1.45      inference('demod', [status(thm)], ['118', '119'])).
% 1.25/1.45  thf('121', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.25/1.45  thf('122', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.25/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.25/1.45  thf('123', plain,
% 1.25/1.45      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.25/1.45          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 1.25/1.45          sk_C)),
% 1.25/1.45      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.25/1.45  thf('124', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.25/1.45      inference('demod', [status(thm)], ['48', '49'])).
% 1.25/1.45  thf('125', plain,
% 1.25/1.45      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.25/1.45         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 1.25/1.45          | ~ (v2_funct_1 @ X28)
% 1.25/1.45          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 1.25/1.45          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 1.25/1.45          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 1.25/1.45          | ~ (v1_funct_1 @ X28))),
% 1.25/1.45      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.25/1.45  thf('126', plain,
% 1.25/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.25/1.45        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.25/1.45        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45            = (k2_funct_1 @ sk_C))
% 1.25/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.25/1.45        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45            != (k2_relat_1 @ sk_C)))),
% 1.25/1.45      inference('sup-', [status(thm)], ['124', '125'])).
% 1.25/1.45  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('128', plain,
% 1.25/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('demod', [status(thm)], ['58', '59'])).
% 1.25/1.45  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('130', plain,
% 1.25/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45         = (k2_relat_1 @ sk_C))),
% 1.25/1.45      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.25/1.45  thf('131', plain,
% 1.25/1.45      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45          = (k2_funct_1 @ sk_C))
% 1.25/1.45        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.25/1.45      inference('demod', [status(thm)], ['126', '127', '128', '129', '130'])).
% 1.25/1.45  thf('132', plain,
% 1.25/1.45      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.25/1.45         = (k2_funct_1 @ sk_C))),
% 1.25/1.45      inference('simplify', [status(thm)], ['131'])).
% 1.25/1.45  thf('133', plain,
% 1.25/1.45      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.25/1.45          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.25/1.45           (k2_funct_1 @ sk_C)) @ 
% 1.25/1.45          sk_C)),
% 1.25/1.45      inference('demod', [status(thm)], ['123', '132'])).
% 1.25/1.45  thf('134', plain,
% 1.25/1.45      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.25/1.45           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 1.25/1.45        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.25/1.45      inference('sup-', [status(thm)], ['111', '133'])).
% 1.25/1.45  thf('135', plain,
% 1.25/1.45      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.25/1.45           sk_C)
% 1.25/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.25/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.25/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.25/1.45        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.25/1.45      inference('sup-', [status(thm)], ['11', '134'])).
% 1.25/1.45  thf('136', plain,
% 1.25/1.45      ((m1_subset_1 @ sk_C @ 
% 1.25/1.45        (k1_zfmisc_1 @ 
% 1.25/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf(redefinition_r2_funct_2, axiom,
% 1.25/1.45    (![A:$i,B:$i,C:$i,D:$i]:
% 1.25/1.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.25/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.25/1.45         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.25/1.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.25/1.45       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.25/1.45  thf('137', plain,
% 1.25/1.45      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.25/1.45         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.25/1.45          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 1.25/1.45          | ~ (v1_funct_1 @ X14)
% 1.25/1.45          | ~ (v1_funct_1 @ X17)
% 1.25/1.45          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 1.25/1.45          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.25/1.45          | (r2_funct_2 @ X15 @ X16 @ X14 @ X17)
% 1.25/1.45          | ((X14) != (X17)))),
% 1.25/1.45      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.25/1.45  thf('138', plain,
% 1.25/1.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.25/1.45         ((r2_funct_2 @ X15 @ X16 @ X17 @ X17)
% 1.25/1.45          | ~ (v1_funct_1 @ X17)
% 1.25/1.45          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 1.25/1.45          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.25/1.45      inference('simplify', [status(thm)], ['137'])).
% 1.25/1.45  thf('139', plain,
% 1.25/1.45      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.25/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.25/1.45        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.25/1.45           sk_C))),
% 1.25/1.45      inference('sup-', [status(thm)], ['136', '138'])).
% 1.25/1.45  thf('140', plain,
% 1.25/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('142', plain,
% 1.25/1.45      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 1.25/1.45      inference('demod', [status(thm)], ['139', '140', '141'])).
% 1.25/1.45  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 1.25/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.25/1.45  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 1.25/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.45  thf('146', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.25/1.45      inference('demod', [status(thm)], ['135', '142', '143', '144', '145'])).
% 1.25/1.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.25/1.45  thf('147', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.25/1.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.25/1.45  thf('148', plain, ($false),
% 1.25/1.45      inference('demod', [status(thm)], ['10', '146', '147'])).
% 1.25/1.45  
% 1.25/1.45  % SZS output end Refutation
% 1.25/1.45  
% 1.32/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
