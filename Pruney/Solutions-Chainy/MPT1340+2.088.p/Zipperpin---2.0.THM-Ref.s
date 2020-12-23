%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mHqezauDMq

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:22 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 668 expanded)
%              Number of leaves         :   41 ( 210 expanded)
%              Depth                    :   23
%              Number of atoms          : 1786 (15405 expanded)
%              Number of equality atoms :  103 ( 495 expanded)
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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

thf('12',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X21 @ X19 )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
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
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','34','37'])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('41',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('44',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('46',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('70',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','62','70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

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

thf('74',plain,(
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

thf('75',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('77',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('81',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('86',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X22 ) @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('90',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('91',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','84','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('96',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('97',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','111'])).

thf('113',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

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

thf('116',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('125',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('127',plain,(
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

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('133',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['125','134'])).

thf('136',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','135'])).

thf('137',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','136'])).

thf('138',plain,(
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

thf('139',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_funct_2 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('140',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_funct_2 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['138','140'])).

thf('142',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['137','144','145','146','147'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('149',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['10','148','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mHqezauDMq
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.36/1.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.36/1.56  % Solved by: fo/fo7.sh
% 1.36/1.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.56  % done 1729 iterations in 1.099s
% 1.36/1.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.36/1.56  % SZS output start Refutation
% 1.36/1.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.36/1.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.36/1.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.36/1.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.36/1.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.36/1.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.36/1.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.36/1.56  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.36/1.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.36/1.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.36/1.56  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.36/1.56  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.36/1.56  thf(sk_C_type, type, sk_C: $i).
% 1.36/1.56  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.56  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.36/1.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.36/1.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.36/1.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.36/1.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.36/1.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.36/1.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.36/1.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.36/1.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.36/1.56  thf(t64_tops_2, conjecture,
% 1.36/1.56    (![A:$i]:
% 1.36/1.56     ( ( l1_struct_0 @ A ) =>
% 1.36/1.56       ( ![B:$i]:
% 1.36/1.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.36/1.56           ( ![C:$i]:
% 1.36/1.56             ( ( ( v1_funct_1 @ C ) & 
% 1.36/1.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                 ( m1_subset_1 @
% 1.36/1.56                   C @ 
% 1.36/1.56                   ( k1_zfmisc_1 @
% 1.36/1.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.36/1.56               ( ( ( ( k2_relset_1 @
% 1.36/1.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.36/1.56                     ( k2_struct_0 @ B ) ) & 
% 1.36/1.56                   ( v2_funct_1 @ C ) ) =>
% 1.36/1.56                 ( r2_funct_2 @
% 1.36/1.56                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.36/1.56                   ( k2_tops_2 @
% 1.36/1.56                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.36/1.56                     ( k2_tops_2 @
% 1.36/1.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 1.36/1.56                   C ) ) ) ) ) ) ))).
% 1.36/1.56  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.56    (~( ![A:$i]:
% 1.36/1.56        ( ( l1_struct_0 @ A ) =>
% 1.36/1.56          ( ![B:$i]:
% 1.36/1.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.36/1.56              ( ![C:$i]:
% 1.36/1.56                ( ( ( v1_funct_1 @ C ) & 
% 1.36/1.56                    ( v1_funct_2 @
% 1.36/1.56                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.36/1.56                    ( m1_subset_1 @
% 1.36/1.56                      C @ 
% 1.36/1.56                      ( k1_zfmisc_1 @
% 1.36/1.56                        ( k2_zfmisc_1 @
% 1.36/1.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.36/1.56                  ( ( ( ( k2_relset_1 @
% 1.36/1.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.36/1.56                        ( k2_struct_0 @ B ) ) & 
% 1.36/1.56                      ( v2_funct_1 @ C ) ) =>
% 1.36/1.56                    ( r2_funct_2 @
% 1.36/1.56                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.36/1.56                      ( k2_tops_2 @
% 1.36/1.56                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.36/1.56                        ( k2_tops_2 @
% 1.36/1.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 1.36/1.56                      C ) ) ) ) ) ) ) )),
% 1.36/1.56    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 1.36/1.56  thf('0', plain,
% 1.36/1.56      ((m1_subset_1 @ sk_C @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf(redefinition_k2_relset_1, axiom,
% 1.36/1.56    (![A:$i,B:$i,C:$i]:
% 1.36/1.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.36/1.56  thf('1', plain,
% 1.36/1.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.36/1.56         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 1.36/1.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.36/1.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.36/1.56  thf('2', plain,
% 1.36/1.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.36/1.56         = (k2_relat_1 @ sk_C))),
% 1.36/1.56      inference('sup-', [status(thm)], ['0', '1'])).
% 1.36/1.56  thf('3', plain,
% 1.36/1.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.36/1.56         = (k2_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup+', [status(thm)], ['2', '3'])).
% 1.36/1.56  thf(fc5_struct_0, axiom,
% 1.36/1.56    (![A:$i]:
% 1.36/1.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.36/1.56       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.36/1.56  thf('5', plain,
% 1.36/1.56      (![X26 : $i]:
% 1.36/1.56         (~ (v1_xboole_0 @ (k2_struct_0 @ X26))
% 1.36/1.56          | ~ (l1_struct_0 @ X26)
% 1.36/1.56          | (v2_struct_0 @ X26))),
% 1.36/1.56      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.36/1.56  thf('6', plain,
% 1.36/1.56      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.36/1.56        | (v2_struct_0 @ sk_B)
% 1.36/1.56        | ~ (l1_struct_0 @ sk_B))),
% 1.36/1.56      inference('sup-', [status(thm)], ['4', '5'])).
% 1.36/1.56  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('8', plain,
% 1.36/1.56      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.36/1.56      inference('demod', [status(thm)], ['6', '7'])).
% 1.36/1.56  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.36/1.56      inference('clc', [status(thm)], ['8', '9'])).
% 1.36/1.56  thf(t65_funct_1, axiom,
% 1.36/1.56    (![A:$i]:
% 1.36/1.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.36/1.56       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.36/1.56  thf('11', plain,
% 1.36/1.56      (![X6 : $i]:
% 1.36/1.56         (~ (v2_funct_1 @ X6)
% 1.36/1.56          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 1.36/1.56          | ~ (v1_funct_1 @ X6)
% 1.36/1.56          | ~ (v1_relat_1 @ X6))),
% 1.36/1.56      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.36/1.56  thf(d3_struct_0, axiom,
% 1.36/1.56    (![A:$i]:
% 1.36/1.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.36/1.56  thf('12', plain,
% 1.36/1.56      (![X25 : $i]:
% 1.36/1.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.36/1.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.56  thf('13', plain,
% 1.36/1.56      (![X25 : $i]:
% 1.36/1.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.36/1.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.56  thf('14', plain,
% 1.36/1.56      ((m1_subset_1 @ sk_C @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('15', plain,
% 1.36/1.56      (((m1_subset_1 @ sk_C @ 
% 1.36/1.56         (k1_zfmisc_1 @ 
% 1.36/1.56          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.36/1.56        | ~ (l1_struct_0 @ sk_A))),
% 1.36/1.56      inference('sup+', [status(thm)], ['13', '14'])).
% 1.36/1.56  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('17', plain,
% 1.36/1.56      ((m1_subset_1 @ sk_C @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('demod', [status(thm)], ['15', '16'])).
% 1.36/1.56  thf(t132_funct_2, axiom,
% 1.36/1.56    (![A:$i,B:$i,C:$i]:
% 1.36/1.56     ( ( ( v1_funct_1 @ C ) & 
% 1.36/1.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.36/1.56       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.36/1.56           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.36/1.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.36/1.56           ( v1_partfun1 @ C @ A ) ) ) ))).
% 1.36/1.56  thf('18', plain,
% 1.36/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.36/1.56         (((X19) = (k1_xboole_0))
% 1.36/1.56          | ~ (v1_funct_1 @ X20)
% 1.36/1.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 1.36/1.56          | (v1_partfun1 @ X20 @ X21)
% 1.36/1.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 1.36/1.56          | ~ (v1_funct_2 @ X20 @ X21 @ X19)
% 1.36/1.56          | ~ (v1_funct_1 @ X20))),
% 1.36/1.56      inference('cnf', [status(esa)], [t132_funct_2])).
% 1.36/1.56  thf('19', plain,
% 1.36/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.36/1.56         (~ (v1_funct_2 @ X20 @ X21 @ X19)
% 1.36/1.56          | (v1_partfun1 @ X20 @ X21)
% 1.36/1.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 1.36/1.56          | ~ (v1_funct_1 @ X20)
% 1.36/1.56          | ((X19) = (k1_xboole_0)))),
% 1.36/1.56      inference('simplify', [status(thm)], ['18'])).
% 1.36/1.56  thf('20', plain,
% 1.36/1.56      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.36/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.36/1.56        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.36/1.56        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['17', '19'])).
% 1.36/1.56  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('22', plain,
% 1.36/1.56      (![X25 : $i]:
% 1.36/1.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.36/1.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.56  thf('23', plain,
% 1.36/1.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('24', plain,
% 1.36/1.56      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.36/1.56        | ~ (l1_struct_0 @ sk_A))),
% 1.36/1.56      inference('sup+', [status(thm)], ['22', '23'])).
% 1.36/1.56  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf('26', plain,
% 1.36/1.56      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.36/1.56      inference('demod', [status(thm)], ['24', '25'])).
% 1.36/1.56  thf('27', plain,
% 1.36/1.56      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.36/1.56        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 1.36/1.56      inference('demod', [status(thm)], ['20', '21', '26'])).
% 1.36/1.56  thf(d4_partfun1, axiom,
% 1.36/1.56    (![A:$i,B:$i]:
% 1.36/1.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.36/1.56       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.36/1.56  thf('28', plain,
% 1.36/1.56      (![X13 : $i, X14 : $i]:
% 1.36/1.56         (~ (v1_partfun1 @ X14 @ X13)
% 1.36/1.56          | ((k1_relat_1 @ X14) = (X13))
% 1.36/1.56          | ~ (v4_relat_1 @ X14 @ X13)
% 1.36/1.56          | ~ (v1_relat_1 @ X14))),
% 1.36/1.56      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.36/1.56  thf('29', plain,
% 1.36/1.56      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.36/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.36/1.56        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.36/1.56        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['27', '28'])).
% 1.36/1.56  thf('30', plain,
% 1.36/1.56      ((m1_subset_1 @ sk_C @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf(cc2_relat_1, axiom,
% 1.36/1.56    (![A:$i]:
% 1.36/1.56     ( ( v1_relat_1 @ A ) =>
% 1.36/1.56       ( ![B:$i]:
% 1.36/1.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.36/1.56  thf('31', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.36/1.56          | (v1_relat_1 @ X0)
% 1.36/1.56          | ~ (v1_relat_1 @ X1))),
% 1.36/1.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.36/1.56  thf('32', plain,
% 1.36/1.56      ((~ (v1_relat_1 @ 
% 1.36/1.56           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.36/1.56        | (v1_relat_1 @ sk_C))),
% 1.36/1.56      inference('sup-', [status(thm)], ['30', '31'])).
% 1.36/1.56  thf(fc6_relat_1, axiom,
% 1.36/1.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.36/1.56  thf('33', plain,
% 1.36/1.56      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.36/1.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.36/1.56  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 1.36/1.56      inference('demod', [status(thm)], ['32', '33'])).
% 1.36/1.56  thf('35', plain,
% 1.36/1.56      ((m1_subset_1 @ sk_C @ 
% 1.36/1.56        (k1_zfmisc_1 @ 
% 1.36/1.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.56      inference('demod', [status(thm)], ['15', '16'])).
% 1.36/1.56  thf(cc2_relset_1, axiom,
% 1.36/1.56    (![A:$i,B:$i,C:$i]:
% 1.36/1.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.36/1.56  thf('36', plain,
% 1.36/1.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.36/1.56         ((v4_relat_1 @ X7 @ X8)
% 1.36/1.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.36/1.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.36/1.56  thf('37', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.36/1.56      inference('sup-', [status(thm)], ['35', '36'])).
% 1.36/1.56  thf('38', plain,
% 1.36/1.56      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.36/1.56        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.36/1.57      inference('demod', [status(thm)], ['29', '34', '37'])).
% 1.36/1.57  thf('39', plain,
% 1.36/1.57      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 1.36/1.57        | ~ (l1_struct_0 @ sk_B)
% 1.36/1.57        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.36/1.57      inference('sup+', [status(thm)], ['12', '38'])).
% 1.36/1.57  thf('40', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['2', '3'])).
% 1.36/1.57  thf('41', plain, ((l1_struct_0 @ sk_B)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('42', plain,
% 1.36/1.57      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.36/1.57        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.36/1.57      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.36/1.57  thf(t55_funct_1, axiom,
% 1.36/1.57    (![A:$i]:
% 1.36/1.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.36/1.57       ( ( v2_funct_1 @ A ) =>
% 1.36/1.57         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.36/1.57           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.36/1.57  thf('43', plain,
% 1.36/1.57      (![X5 : $i]:
% 1.36/1.57         (~ (v2_funct_1 @ X5)
% 1.36/1.57          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 1.36/1.57          | ~ (v1_funct_1 @ X5)
% 1.36/1.57          | ~ (v1_relat_1 @ X5))),
% 1.36/1.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.36/1.57  thf('44', plain,
% 1.36/1.57      (![X25 : $i]:
% 1.36/1.57         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.36/1.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.57  thf(fc6_funct_1, axiom,
% 1.36/1.57    (![A:$i]:
% 1.36/1.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 1.36/1.57       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.36/1.57         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 1.36/1.57         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.36/1.57  thf('45', plain,
% 1.36/1.57      (![X4 : $i]:
% 1.36/1.57         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 1.36/1.57          | ~ (v2_funct_1 @ X4)
% 1.36/1.57          | ~ (v1_funct_1 @ X4)
% 1.36/1.57          | ~ (v1_relat_1 @ X4))),
% 1.36/1.57      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.36/1.57  thf('46', plain,
% 1.36/1.57      (![X25 : $i]:
% 1.36/1.57         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.36/1.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.57  thf('47', plain,
% 1.36/1.57      ((m1_subset_1 @ sk_C @ 
% 1.36/1.57        (k1_zfmisc_1 @ 
% 1.36/1.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('48', plain,
% 1.36/1.57      (((m1_subset_1 @ sk_C @ 
% 1.36/1.57         (k1_zfmisc_1 @ 
% 1.36/1.57          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.36/1.57        | ~ (l1_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['46', '47'])).
% 1.36/1.57  thf('49', plain, ((l1_struct_0 @ sk_B)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('50', plain,
% 1.36/1.57      ((m1_subset_1 @ sk_C @ 
% 1.36/1.57        (k1_zfmisc_1 @ 
% 1.36/1.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.36/1.57      inference('demod', [status(thm)], ['48', '49'])).
% 1.36/1.57  thf('51', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['2', '3'])).
% 1.36/1.57  thf('52', plain,
% 1.36/1.57      ((m1_subset_1 @ sk_C @ 
% 1.36/1.57        (k1_zfmisc_1 @ 
% 1.36/1.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.36/1.57      inference('demod', [status(thm)], ['50', '51'])).
% 1.36/1.57  thf(t31_funct_2, axiom,
% 1.36/1.57    (![A:$i,B:$i,C:$i]:
% 1.36/1.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.36/1.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.36/1.57       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.36/1.57         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.36/1.57           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.36/1.57           ( m1_subset_1 @
% 1.36/1.57             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.36/1.57  thf('53', plain,
% 1.36/1.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.36/1.57         (~ (v2_funct_1 @ X22)
% 1.36/1.57          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 1.36/1.57          | (m1_subset_1 @ (k2_funct_1 @ X22) @ 
% 1.36/1.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.36/1.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.36/1.57          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 1.36/1.57          | ~ (v1_funct_1 @ X22))),
% 1.36/1.57      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.36/1.57  thf('54', plain,
% 1.36/1.57      ((~ (v1_funct_1 @ sk_C)
% 1.36/1.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.36/1.57        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.36/1.57           (k1_zfmisc_1 @ 
% 1.36/1.57            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 1.36/1.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57            != (k2_relat_1 @ sk_C))
% 1.36/1.57        | ~ (v2_funct_1 @ sk_C))),
% 1.36/1.57      inference('sup-', [status(thm)], ['52', '53'])).
% 1.36/1.57  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('56', plain,
% 1.36/1.57      (![X25 : $i]:
% 1.36/1.57         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.36/1.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.57  thf('57', plain,
% 1.36/1.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('58', plain,
% 1.36/1.57      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.36/1.57        | ~ (l1_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['56', '57'])).
% 1.36/1.57  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('60', plain,
% 1.36/1.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('demod', [status(thm)], ['58', '59'])).
% 1.36/1.57  thf('61', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['2', '3'])).
% 1.36/1.57  thf('62', plain,
% 1.36/1.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.36/1.57      inference('demod', [status(thm)], ['60', '61'])).
% 1.36/1.57  thf('63', plain,
% 1.36/1.57      (![X25 : $i]:
% 1.36/1.57         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.36/1.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.57  thf('64', plain,
% 1.36/1.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.36/1.57         = (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('65', plain,
% 1.36/1.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.36/1.57          = (k2_struct_0 @ sk_B))
% 1.36/1.57        | ~ (l1_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['63', '64'])).
% 1.36/1.57  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('67', plain,
% 1.36/1.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.36/1.57         = (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('demod', [status(thm)], ['65', '66'])).
% 1.36/1.57  thf('68', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['2', '3'])).
% 1.36/1.57  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['2', '3'])).
% 1.36/1.57  thf('70', plain,
% 1.36/1.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57         = (k2_relat_1 @ sk_C))),
% 1.36/1.57      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.36/1.57  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('72', plain,
% 1.36/1.57      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.36/1.57         (k1_zfmisc_1 @ 
% 1.36/1.57          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 1.36/1.57        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.36/1.57      inference('demod', [status(thm)], ['54', '55', '62', '70', '71'])).
% 1.36/1.57  thf('73', plain,
% 1.36/1.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.36/1.57        (k1_zfmisc_1 @ 
% 1.36/1.57         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 1.36/1.57      inference('simplify', [status(thm)], ['72'])).
% 1.36/1.57  thf(d4_tops_2, axiom,
% 1.36/1.57    (![A:$i,B:$i,C:$i]:
% 1.36/1.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.36/1.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.36/1.57       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.36/1.57         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.36/1.57  thf('74', plain,
% 1.36/1.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.36/1.57         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.36/1.57          | ~ (v2_funct_1 @ X29)
% 1.36/1.57          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.36/1.57          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.36/1.57          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.36/1.57          | ~ (v1_funct_1 @ X29))),
% 1.36/1.57      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.36/1.57  thf('75', plain,
% 1.36/1.57      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.36/1.57        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.36/1.57             (u1_struct_0 @ sk_A))
% 1.36/1.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.36/1.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.36/1.57        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 1.36/1.57      inference('sup-', [status(thm)], ['73', '74'])).
% 1.36/1.57  thf('76', plain,
% 1.36/1.57      ((m1_subset_1 @ sk_C @ 
% 1.36/1.57        (k1_zfmisc_1 @ 
% 1.36/1.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.36/1.57      inference('demod', [status(thm)], ['50', '51'])).
% 1.36/1.57  thf('77', plain,
% 1.36/1.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.36/1.57         (~ (v2_funct_1 @ X22)
% 1.36/1.57          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 1.36/1.57          | (v1_funct_1 @ (k2_funct_1 @ X22))
% 1.36/1.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.36/1.57          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 1.36/1.57          | ~ (v1_funct_1 @ X22))),
% 1.36/1.57      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.36/1.57  thf('78', plain,
% 1.36/1.57      ((~ (v1_funct_1 @ sk_C)
% 1.36/1.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.36/1.57        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.36/1.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57            != (k2_relat_1 @ sk_C))
% 1.36/1.57        | ~ (v2_funct_1 @ sk_C))),
% 1.36/1.57      inference('sup-', [status(thm)], ['76', '77'])).
% 1.36/1.57  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('80', plain,
% 1.36/1.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.36/1.57      inference('demod', [status(thm)], ['60', '61'])).
% 1.36/1.57  thf('81', plain,
% 1.36/1.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57         = (k2_relat_1 @ sk_C))),
% 1.36/1.57      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.36/1.57  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('83', plain,
% 1.36/1.57      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.36/1.57        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.36/1.57      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 1.36/1.57  thf('84', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.36/1.57      inference('simplify', [status(thm)], ['83'])).
% 1.36/1.57  thf('85', plain,
% 1.36/1.57      ((m1_subset_1 @ sk_C @ 
% 1.36/1.57        (k1_zfmisc_1 @ 
% 1.36/1.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.36/1.57      inference('demod', [status(thm)], ['50', '51'])).
% 1.36/1.57  thf('86', plain,
% 1.36/1.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.36/1.57         (~ (v2_funct_1 @ X22)
% 1.36/1.57          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 1.36/1.57          | (v1_funct_2 @ (k2_funct_1 @ X22) @ X23 @ X24)
% 1.36/1.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 1.36/1.57          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 1.36/1.57          | ~ (v1_funct_1 @ X22))),
% 1.36/1.57      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.36/1.57  thf('87', plain,
% 1.36/1.57      ((~ (v1_funct_1 @ sk_C)
% 1.36/1.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.36/1.57        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.36/1.57           (u1_struct_0 @ sk_A))
% 1.36/1.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57            != (k2_relat_1 @ sk_C))
% 1.36/1.57        | ~ (v2_funct_1 @ sk_C))),
% 1.36/1.57      inference('sup-', [status(thm)], ['85', '86'])).
% 1.36/1.57  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('89', plain,
% 1.36/1.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.36/1.57      inference('demod', [status(thm)], ['60', '61'])).
% 1.36/1.57  thf('90', plain,
% 1.36/1.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57         = (k2_relat_1 @ sk_C))),
% 1.36/1.57      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.36/1.57  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('92', plain,
% 1.36/1.57      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.36/1.57         (u1_struct_0 @ sk_A))
% 1.36/1.57        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.36/1.57      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 1.36/1.57  thf('93', plain,
% 1.36/1.57      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.36/1.57        (u1_struct_0 @ sk_A))),
% 1.36/1.57      inference('simplify', [status(thm)], ['92'])).
% 1.36/1.57  thf('94', plain,
% 1.36/1.57      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.36/1.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.36/1.57        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 1.36/1.57      inference('demod', [status(thm)], ['75', '84', '93'])).
% 1.36/1.57  thf('95', plain,
% 1.36/1.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.36/1.57        (k1_zfmisc_1 @ 
% 1.36/1.57         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 1.36/1.57      inference('simplify', [status(thm)], ['72'])).
% 1.36/1.57  thf('96', plain,
% 1.36/1.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.36/1.57         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 1.36/1.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.36/1.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.36/1.57  thf('97', plain,
% 1.36/1.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.36/1.57      inference('sup-', [status(thm)], ['95', '96'])).
% 1.36/1.57  thf('98', plain,
% 1.36/1.57      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.36/1.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.36/1.57        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 1.36/1.57      inference('demod', [status(thm)], ['94', '97'])).
% 1.36/1.57  thf('99', plain,
% 1.36/1.57      ((~ (v1_relat_1 @ sk_C)
% 1.36/1.57        | ~ (v1_funct_1 @ sk_C)
% 1.36/1.57        | ~ (v2_funct_1 @ sk_C)
% 1.36/1.57        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 1.36/1.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.36/1.57      inference('sup-', [status(thm)], ['45', '98'])).
% 1.36/1.57  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 1.36/1.57      inference('demod', [status(thm)], ['32', '33'])).
% 1.36/1.57  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('102', plain, ((v2_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('103', plain,
% 1.36/1.57      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 1.36/1.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.36/1.57      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 1.36/1.57  thf('104', plain,
% 1.36/1.57      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 1.36/1.57        | ~ (l1_struct_0 @ sk_A)
% 1.36/1.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.36/1.57      inference('sup-', [status(thm)], ['44', '103'])).
% 1.36/1.57  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('106', plain,
% 1.36/1.57      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 1.36/1.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.36/1.57      inference('demod', [status(thm)], ['104', '105'])).
% 1.36/1.57  thf('107', plain,
% 1.36/1.57      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 1.36/1.57        | ~ (v1_relat_1 @ sk_C)
% 1.36/1.57        | ~ (v1_funct_1 @ sk_C)
% 1.36/1.57        | ~ (v2_funct_1 @ sk_C)
% 1.36/1.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.36/1.57      inference('sup-', [status(thm)], ['43', '106'])).
% 1.36/1.57  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 1.36/1.57      inference('demod', [status(thm)], ['32', '33'])).
% 1.36/1.57  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('111', plain,
% 1.36/1.57      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 1.36/1.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.36/1.57      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 1.36/1.57  thf('112', plain,
% 1.36/1.57      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.36/1.57        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.36/1.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.36/1.57      inference('sup-', [status(thm)], ['42', '111'])).
% 1.36/1.57  thf('113', plain,
% 1.36/1.57      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.36/1.57        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.36/1.57      inference('simplify', [status(thm)], ['112'])).
% 1.36/1.57  thf('114', plain,
% 1.36/1.57      (![X25 : $i]:
% 1.36/1.57         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.36/1.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.57  thf('115', plain,
% 1.36/1.57      (![X25 : $i]:
% 1.36/1.57         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.36/1.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.57  thf('116', plain,
% 1.36/1.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.57          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 1.36/1.57          sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('117', plain,
% 1.36/1.57      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.57           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 1.36/1.57           sk_C)
% 1.36/1.57        | ~ (l1_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup-', [status(thm)], ['115', '116'])).
% 1.36/1.57  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('119', plain,
% 1.36/1.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.57          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 1.36/1.57          sk_C)),
% 1.36/1.57      inference('demod', [status(thm)], ['117', '118'])).
% 1.36/1.57  thf('120', plain,
% 1.36/1.57      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.57           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 1.36/1.57           sk_C)
% 1.36/1.57        | ~ (l1_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup-', [status(thm)], ['114', '119'])).
% 1.36/1.57  thf('121', plain, ((l1_struct_0 @ sk_B)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('122', plain,
% 1.36/1.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.57          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 1.36/1.57          sk_C)),
% 1.36/1.57      inference('demod', [status(thm)], ['120', '121'])).
% 1.36/1.57  thf('123', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['2', '3'])).
% 1.36/1.57  thf('124', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.36/1.57      inference('sup+', [status(thm)], ['2', '3'])).
% 1.36/1.57  thf('125', plain,
% 1.36/1.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.57          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 1.36/1.57          sk_C)),
% 1.36/1.57      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.36/1.57  thf('126', plain,
% 1.36/1.57      ((m1_subset_1 @ sk_C @ 
% 1.36/1.57        (k1_zfmisc_1 @ 
% 1.36/1.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.36/1.57      inference('demod', [status(thm)], ['50', '51'])).
% 1.36/1.57  thf('127', plain,
% 1.36/1.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.36/1.57         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.36/1.57          | ~ (v2_funct_1 @ X29)
% 1.36/1.57          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.36/1.57          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.36/1.57          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.36/1.57          | ~ (v1_funct_1 @ X29))),
% 1.36/1.57      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.36/1.57  thf('128', plain,
% 1.36/1.57      ((~ (v1_funct_1 @ sk_C)
% 1.36/1.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.36/1.57        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57            = (k2_funct_1 @ sk_C))
% 1.36/1.57        | ~ (v2_funct_1 @ sk_C)
% 1.36/1.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57            != (k2_relat_1 @ sk_C)))),
% 1.36/1.57      inference('sup-', [status(thm)], ['126', '127'])).
% 1.36/1.57  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('130', plain,
% 1.36/1.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.36/1.57      inference('demod', [status(thm)], ['60', '61'])).
% 1.36/1.57  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('132', plain,
% 1.36/1.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57         = (k2_relat_1 @ sk_C))),
% 1.36/1.57      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.36/1.57  thf('133', plain,
% 1.36/1.57      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57          = (k2_funct_1 @ sk_C))
% 1.36/1.57        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.36/1.57      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 1.36/1.57  thf('134', plain,
% 1.36/1.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.36/1.57         = (k2_funct_1 @ sk_C))),
% 1.36/1.57      inference('simplify', [status(thm)], ['133'])).
% 1.36/1.57  thf('135', plain,
% 1.36/1.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.57          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.36/1.57           (k2_funct_1 @ sk_C)) @ 
% 1.36/1.57          sk_C)),
% 1.36/1.57      inference('demod', [status(thm)], ['125', '134'])).
% 1.36/1.57  thf('136', plain,
% 1.36/1.57      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.36/1.57           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 1.36/1.57        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.36/1.57      inference('sup-', [status(thm)], ['113', '135'])).
% 1.36/1.57  thf('137', plain,
% 1.36/1.57      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.36/1.57           sk_C)
% 1.36/1.57        | ~ (v1_relat_1 @ sk_C)
% 1.36/1.57        | ~ (v1_funct_1 @ sk_C)
% 1.36/1.57        | ~ (v2_funct_1 @ sk_C)
% 1.36/1.57        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.36/1.57      inference('sup-', [status(thm)], ['11', '136'])).
% 1.36/1.57  thf('138', plain,
% 1.36/1.57      ((m1_subset_1 @ sk_C @ 
% 1.36/1.57        (k1_zfmisc_1 @ 
% 1.36/1.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf(redefinition_r2_funct_2, axiom,
% 1.36/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.36/1.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.36/1.57         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.36/1.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.36/1.57       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.36/1.57  thf('139', plain,
% 1.36/1.57      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.36/1.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.36/1.57          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 1.36/1.57          | ~ (v1_funct_1 @ X15)
% 1.36/1.57          | ~ (v1_funct_1 @ X18)
% 1.36/1.57          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 1.36/1.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.36/1.57          | (r2_funct_2 @ X16 @ X17 @ X15 @ X18)
% 1.36/1.57          | ((X15) != (X18)))),
% 1.36/1.57      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.36/1.57  thf('140', plain,
% 1.36/1.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.36/1.57         ((r2_funct_2 @ X16 @ X17 @ X18 @ X18)
% 1.36/1.57          | ~ (v1_funct_1 @ X18)
% 1.36/1.57          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 1.36/1.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.36/1.57      inference('simplify', [status(thm)], ['139'])).
% 1.36/1.57  thf('141', plain,
% 1.36/1.57      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.36/1.57        | ~ (v1_funct_1 @ sk_C)
% 1.36/1.57        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 1.36/1.57           sk_C))),
% 1.36/1.57      inference('sup-', [status(thm)], ['138', '140'])).
% 1.36/1.57  thf('142', plain,
% 1.36/1.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('144', plain,
% 1.36/1.57      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 1.36/1.57      inference('demod', [status(thm)], ['141', '142', '143'])).
% 1.36/1.57  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 1.36/1.57      inference('demod', [status(thm)], ['32', '33'])).
% 1.36/1.57  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 1.36/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.57  thf('148', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.36/1.57      inference('demod', [status(thm)], ['137', '144', '145', '146', '147'])).
% 1.36/1.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.36/1.57  thf('149', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.57  thf('150', plain, ($false),
% 1.36/1.57      inference('demod', [status(thm)], ['10', '148', '149'])).
% 1.36/1.57  
% 1.36/1.57  % SZS output end Refutation
% 1.36/1.57  
% 1.36/1.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
