%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wmtwaYkaIl

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  192 (1406 expanded)
%              Number of leaves         :   37 ( 423 expanded)
%              Depth                    :   23
%              Number of atoms          : 1872 (34595 expanded)
%              Number of equality atoms :  126 (1727 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X13 @ ( k3_relset_1 @ X13 @ X14 @ X15 ) )
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k3_relset_1 @ X11 @ X12 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('9',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','19','22'])).

thf('24',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','40'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','47'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('49',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['23','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('59',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X23 @ X25 )
       != X23 )
      | ~ ( v2_funct_1 @ X25 )
      | ( ( k2_tops_2 @ X24 @ X23 @ X25 )
        = ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('76',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','64','65','76'])).

thf('78',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('80',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('92',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('99',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','105'])).

thf('107',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('108',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('112',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('114',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('115',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','119'])).

thf('121',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','120'])).

thf('122',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('124',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['82'])).

thf('127',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','132'])).

thf('134',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('135',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('138',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X13 @ ( k3_relset_1 @ X13 @ X14 @ X15 ) )
        = ( k2_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('139',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('141',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('143',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('144',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','18'])).

thf('145',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('146',plain,
    ( ( k3_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['141','142','143','146'])).

thf('148',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','147'])).

thf('149',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['82'])).

thf('151',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['149','150'])).

thf('152',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['121','151'])).

thf('153',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wmtwaYkaIl
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 256 iterations in 0.081s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.55  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.22/0.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(d3_struct_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf(t62_tops_2, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_struct_0 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                 ( m1_subset_1 @
% 0.22/0.55                   C @ 
% 0.22/0.55                   ( k1_zfmisc_1 @
% 0.22/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55               ( ( ( ( k2_relset_1 @
% 0.22/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.22/0.55                     ( k2_struct_0 @ B ) ) & 
% 0.22/0.55                   ( v2_funct_1 @ C ) ) =>
% 0.22/0.55                 ( ( ( k1_relset_1 @
% 0.22/0.55                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.55                       ( k2_tops_2 @
% 0.22/0.55                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.22/0.55                     ( k2_struct_0 @ B ) ) & 
% 0.22/0.55                   ( ( k2_relset_1 @
% 0.22/0.55                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.55                       ( k2_tops_2 @
% 0.22/0.55                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.22/0.55                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( l1_struct_0 @ A ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.22/0.55              ( ![C:$i]:
% 0.22/0.55                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.55                    ( v1_funct_2 @
% 0.22/0.55                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                    ( m1_subset_1 @
% 0.22/0.55                      C @ 
% 0.22/0.55                      ( k1_zfmisc_1 @
% 0.22/0.55                        ( k2_zfmisc_1 @
% 0.22/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55                  ( ( ( ( k2_relset_1 @
% 0.22/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.22/0.55                        ( k2_struct_0 @ B ) ) & 
% 0.22/0.55                      ( v2_funct_1 @ C ) ) =>
% 0.22/0.55                    ( ( ( k1_relset_1 @
% 0.22/0.55                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.55                          ( k2_tops_2 @
% 0.22/0.55                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.22/0.55                        ( k2_struct_0 @ B ) ) & 
% 0.22/0.55                      ( ( k2_relset_1 @
% 0.22/0.55                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.55                          ( k2_tops_2 @
% 0.22/0.55                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.22/0.55                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (((m1_subset_1 @ sk_C @ 
% 0.22/0.55         (k1_zfmisc_1 @ 
% 0.22/0.55          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.55  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf(t24_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.22/0.55           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.55         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.22/0.55           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         (((k2_relset_1 @ X14 @ X13 @ (k3_relset_1 @ X13 @ X14 @ X15))
% 0.22/0.55            = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.22/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.22/0.55      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf(redefinition_k3_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.55         (((k3_relset_1 @ X11 @ X12 @ X10) = (k4_relat_1 @ X10))
% 0.22/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k4_relat_1 @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.55  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d9_funct_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v2_funct_1 @ X0)
% 0.22/0.55          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 0.22/0.55          | ~ (v1_funct_1 @ X0)
% 0.22/0.55          | ~ (v1_relat_1 @ X0))),
% 0.22/0.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.55        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.22/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.22/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(cc1_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55       ( v1_relat_1 @ C ) ))).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         ((v1_relat_1 @ X1)
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.55  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('18', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['14', '17'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_funct_1 @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['9', '18'])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.55         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.22/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k1_relat_1 @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['6', '19', '22'])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      (((m1_subset_1 @ sk_C @ 
% 0.22/0.55         (k1_zfmisc_1 @ 
% 0.22/0.55          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.55  thf(cc5_funct_2, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.55       ( ![C:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.22/0.55             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.22/0.55          | (v1_partfun1 @ X16 @ X17)
% 0.22/0.55          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.22/0.55          | ~ (v1_funct_1 @ X16)
% 0.22/0.55          | (v1_xboole_0 @ X18))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.55        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.55  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.55  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['32', '37'])).
% 0.22/0.55  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['30', '31', '40'])).
% 0.22/0.55  thf(d4_partfun1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.55       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (![X19 : $i, X20 : $i]:
% 0.22/0.55         (~ (v1_partfun1 @ X20 @ X19)
% 0.22/0.55          | ((k1_relat_1 @ X20) = (X19))
% 0.22/0.55          | ~ (v4_relat_1 @ X20 @ X19)
% 0.22/0.55          | ~ (v1_relat_1 @ X20))),
% 0.22/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.55        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.22/0.55        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.55  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf(cc2_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.55         ((v4_relat_1 @ X4 @ X5)
% 0.22/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.55  thf('47', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.22/0.55  thf(fc5_struct_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (![X22 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ (k2_struct_0 @ X22))
% 0.22/0.55          | ~ (l1_struct_0 @ X22)
% 0.22/0.55          | (v2_struct_0 @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.22/0.55  thf('50', plain,
% 0.22/0.55      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.22/0.55        | (v2_struct_0 @ sk_B)
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.55  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.55  thf('53', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('54', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['23', '54'])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.55  thf('57', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf(d4_tops_2, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.55       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.22/0.55         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.55         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 0.22/0.55          | ~ (v2_funct_1 @ X25)
% 0.22/0.55          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 0.22/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.22/0.55          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 0.22/0.55          | ~ (v1_funct_1 @ X25))),
% 0.22/0.55      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.22/0.55  thf('60', plain,
% 0.22/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.22/0.55        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55            = (k2_funct_1 @ sk_C))
% 0.22/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.22/0.55        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55            != (k2_struct_0 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('62', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.55  thf('63', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('64', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.22/0.55  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55          = (k2_struct_0 @ sk_B))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup+', [status(thm)], ['67', '68'])).
% 0.22/0.55  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.55  thf('72', plain,
% 0.22/0.55      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55          = (k2_struct_0 @ sk_B))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['66', '71'])).
% 0.22/0.55  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('74', plain,
% 0.22/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.55  thf('75', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['74', '75'])).
% 0.22/0.55  thf('77', plain,
% 0.22/0.55      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55          = (k2_funct_1 @ sk_C))
% 0.22/0.55        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['60', '61', '64', '65', '76'])).
% 0.22/0.55  thf('78', plain,
% 0.22/0.55      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_funct_1 @ sk_C))),
% 0.22/0.55      inference('simplify', [status(thm)], ['77'])).
% 0.22/0.55  thf('79', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('80', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('81', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('82', plain,
% 0.22/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_B))
% 0.22/0.55        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55            != (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('83', plain,
% 0.22/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_A)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('split', [status(esa)], ['82'])).
% 0.22/0.55  thf('84', plain,
% 0.22/0.55      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55           != (k2_struct_0 @ sk_A))
% 0.22/0.55         | ~ (l1_struct_0 @ sk_A)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['81', '83'])).
% 0.22/0.55  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('86', plain,
% 0.22/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_A)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['84', '85'])).
% 0.22/0.55  thf('87', plain,
% 0.22/0.55      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55           != (k2_struct_0 @ sk_A))
% 0.22/0.55         | ~ (l1_struct_0 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['80', '86'])).
% 0.22/0.55  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('89', plain,
% 0.22/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_A)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.22/0.55  thf('90', plain,
% 0.22/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_A)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['79', '89'])).
% 0.22/0.55  thf('91', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('92', plain,
% 0.22/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k1_relat_1 @ sk_C)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.55  thf('93', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('94', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('95', plain,
% 0.22/0.55      (((m1_subset_1 @ sk_C @ 
% 0.22/0.55         (k1_zfmisc_1 @ 
% 0.22/0.55          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['93', '94'])).
% 0.22/0.55  thf('96', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('97', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['95', '96'])).
% 0.22/0.55  thf('98', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.22/0.55          | (v1_partfun1 @ X16 @ X17)
% 0.22/0.55          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.22/0.55          | ~ (v1_funct_1 @ X16)
% 0.22/0.55          | (v1_xboole_0 @ X18))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.22/0.55  thf('99', plain,
% 0.22/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.55        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['97', '98'])).
% 0.22/0.55  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('101', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('102', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('103', plain,
% 0.22/0.55      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['101', '102'])).
% 0.22/0.55  thf('104', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('105', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['103', '104'])).
% 0.22/0.55  thf('106', plain,
% 0.22/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['99', '100', '105'])).
% 0.22/0.55  thf('107', plain,
% 0.22/0.55      (![X19 : $i, X20 : $i]:
% 0.22/0.55         (~ (v1_partfun1 @ X20 @ X19)
% 0.22/0.55          | ((k1_relat_1 @ X20) = (X19))
% 0.22/0.55          | ~ (v4_relat_1 @ X20 @ X19)
% 0.22/0.55          | ~ (v1_relat_1 @ X20))),
% 0.22/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.55  thf('108', plain,
% 0.22/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.55        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.22/0.55        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.22/0.55  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('110', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('111', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.55         ((v4_relat_1 @ X4 @ X5)
% 0.22/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.55  thf('112', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['110', '111'])).
% 0.22/0.55  thf('113', plain,
% 0.22/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.22/0.55        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['108', '109', '112'])).
% 0.22/0.55  thf('114', plain,
% 0.22/0.55      (![X22 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ (k2_struct_0 @ X22))
% 0.22/0.55          | ~ (l1_struct_0 @ X22)
% 0.22/0.55          | (v2_struct_0 @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.22/0.55  thf('115', plain,
% 0.22/0.55      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.22/0.55        | (v2_struct_0 @ sk_B)
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['113', '114'])).
% 0.22/0.55  thf('116', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('117', plain,
% 0.22/0.55      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['115', '116'])).
% 0.22/0.55  thf('118', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('119', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['117', '118'])).
% 0.22/0.55  thf('120', plain,
% 0.22/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k1_relat_1 @ sk_C)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['92', '119'])).
% 0.22/0.55  thf('121', plain,
% 0.22/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['78', '120'])).
% 0.22/0.55  thf('122', plain,
% 0.22/0.55      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_funct_1 @ sk_C))),
% 0.22/0.55      inference('simplify', [status(thm)], ['77'])).
% 0.22/0.55  thf('123', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('124', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('125', plain,
% 0.22/0.55      (![X21 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('126', plain,
% 0.22/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['82'])).
% 0.22/0.55  thf('127', plain,
% 0.22/0.55      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55           != (k2_struct_0 @ sk_B))
% 0.22/0.55         | ~ (l1_struct_0 @ sk_A)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['125', '126'])).
% 0.22/0.55  thf('128', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('129', plain,
% 0.22/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['127', '128'])).
% 0.22/0.55  thf('130', plain,
% 0.22/0.55      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55           != (k2_struct_0 @ sk_B))
% 0.22/0.55         | ~ (l1_struct_0 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['124', '129'])).
% 0.22/0.55  thf('131', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('132', plain,
% 0.22/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['130', '131'])).
% 0.22/0.55  thf('133', plain,
% 0.22/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['123', '132'])).
% 0.22/0.55  thf('134', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['117', '118'])).
% 0.22/0.55  thf('135', plain,
% 0.22/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          != (k2_struct_0 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['133', '134'])).
% 0.22/0.55  thf('136', plain,
% 0.22/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['122', '135'])).
% 0.22/0.55  thf('137', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf('138', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         (((k1_relset_1 @ X14 @ X13 @ (k3_relset_1 @ X13 @ X14 @ X15))
% 0.22/0.55            = (k2_relset_1 @ X13 @ X14 @ X15))
% 0.22/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.22/0.55      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.22/0.55  thf('139', plain,
% 0.22/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55         = (k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['137', '138'])).
% 0.22/0.55  thf('140', plain,
% 0.22/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.55  thf('141', plain,
% 0.22/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.55         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55         = (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['139', '140'])).
% 0.22/0.55  thf('142', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('143', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('144', plain,
% 0.22/0.55      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_funct_1 @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['9', '18'])).
% 0.22/0.55  thf('145', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('146', plain,
% 0.22/0.55      (((k3_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.55         = (k2_funct_1 @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['144', '145'])).
% 0.22/0.55  thf('147', plain,
% 0.22/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['141', '142', '143', '146'])).
% 0.22/0.55  thf('148', plain,
% 0.22/0.55      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55                = (k2_struct_0 @ sk_B))))),
% 0.22/0.55      inference('demod', [status(thm)], ['136', '147'])).
% 0.22/0.55  thf('149', plain,
% 0.22/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          = (k2_struct_0 @ sk_B)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['148'])).
% 0.22/0.55  thf('150', plain,
% 0.22/0.55      (~
% 0.22/0.55       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          = (k2_struct_0 @ sk_A))) | 
% 0.22/0.55       ~
% 0.22/0.55       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          = (k2_struct_0 @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['82'])).
% 0.22/0.55  thf('151', plain,
% 0.22/0.55      (~
% 0.22/0.55       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.22/0.55          = (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['149', '150'])).
% 0.22/0.55  thf('152', plain,
% 0.22/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.22/0.55         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['121', '151'])).
% 0.22/0.55  thf('153', plain, ($false),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['55', '152'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
