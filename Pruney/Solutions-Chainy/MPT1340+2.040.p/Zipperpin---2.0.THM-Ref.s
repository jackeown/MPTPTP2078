%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wDDqjyPZr0

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:12 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  253 ( 856 expanded)
%              Number of leaves         :   41 ( 264 expanded)
%              Depth                    :   36
%              Number of atoms          : 2691 (19619 expanded)
%              Number of equality atoms :  151 ( 637 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

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
    inference('sup+',[status(thm)],['2','3'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( ( k5_relat_1 @ X21 @ ( k2_funct_1 @ X21 ) )
        = ( k6_partfun1 @ X22 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X22 @ X20 @ X21 )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k6_partfun1 @ X12 )
      = ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ( ( k5_relat_1 @ X21 @ ( k2_funct_1 @ X21 ) )
        = ( k6_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X22 @ X20 @ X21 )
       != X20 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('30',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','30','31','38','39'])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('43',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('44',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','47','48','49'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X2: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relset_1 @ X19 @ X18 @ X17 )
       != X18 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
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
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('57',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

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

thf('61',plain,(
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

thf('62',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relset_1 @ X19 @ X18 @ X17 )
       != X18 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('70',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('78',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relset_1 @ X19 @ X18 @ X17 )
       != X18 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X17 ) @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('82',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('87',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('88',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('90',plain,(
    ! [X2: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('91',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('92',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('93',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('94',plain,(
    ! [X2: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('95',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('96',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('97',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('98',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['92','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['91','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['90','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['89','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ! [X2: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('125',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['124','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X2: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('132',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('133',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('135',plain,(
    ! [X2: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('136',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('137',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('138',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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

thf('139',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k1_relat_1 @ X3 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
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
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
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
    inference('sup-',[status(thm)],['136','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['135','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['133','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['132','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['131','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['123','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','160'])).

thf('162',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','76','85','161'])).

thf('163',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['51','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['50','167'])).

thf('169',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('171',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('177',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('179',plain,(
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

thf('180',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('185',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['177','186'])).

thf('188',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['170','187'])).

thf('189',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('190',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['169','191'])).

thf('193',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','192'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
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

thf('196',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_funct_2 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['194','200'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['193','204','205','206','207'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('209',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('210',plain,(
    $false ),
    inference(demod,[status(thm)],['10','208','209'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wDDqjyPZr0
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 1558 iterations in 0.473s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.93  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.75/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.93  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.75/0.93  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.75/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.93  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.75/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.93  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/0.93  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.75/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.93  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.75/0.93  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.93  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.75/0.93  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.93  thf(t64_tops_2, conjecture,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( l1_struct_0 @ A ) =>
% 0.75/0.93       ( ![B:$i]:
% 0.75/0.93         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.75/0.93           ( ![C:$i]:
% 0.75/0.93             ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.93                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/0.93                 ( m1_subset_1 @
% 0.75/0.93                   C @ 
% 0.75/0.93                   ( k1_zfmisc_1 @
% 0.75/0.93                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/0.93               ( ( ( ( k2_relset_1 @
% 0.75/0.93                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.75/0.93                     ( k2_struct_0 @ B ) ) & 
% 0.75/0.93                   ( v2_funct_1 @ C ) ) =>
% 0.75/0.93                 ( r2_funct_2 @
% 0.75/0.93                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.75/0.93                   ( k2_tops_2 @
% 0.75/0.93                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.93                     ( k2_tops_2 @
% 0.75/0.93                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.75/0.93                   C ) ) ) ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.93    (~( ![A:$i]:
% 0.75/0.93        ( ( l1_struct_0 @ A ) =>
% 0.75/0.93          ( ![B:$i]:
% 0.75/0.93            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.75/0.93              ( ![C:$i]:
% 0.75/0.93                ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.93                    ( v1_funct_2 @
% 0.75/0.93                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/0.93                    ( m1_subset_1 @
% 0.75/0.93                      C @ 
% 0.75/0.93                      ( k1_zfmisc_1 @
% 0.75/0.93                        ( k2_zfmisc_1 @
% 0.75/0.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/0.93                  ( ( ( ( k2_relset_1 @
% 0.75/0.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.75/0.93                        ( k2_struct_0 @ B ) ) & 
% 0.75/0.93                      ( v2_funct_1 @ C ) ) =>
% 0.75/0.93                    ( r2_funct_2 @
% 0.75/0.93                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.75/0.93                      ( k2_tops_2 @
% 0.75/0.93                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.93                        ( k2_tops_2 @
% 0.75/0.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.75/0.93                      C ) ) ) ) ) ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.75/0.93  thf('0', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(redefinition_k2_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.75/0.93  thf('1', plain,
% 0.75/0.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.93         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.75/0.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.93         = (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.93         = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.93  thf(fc5_struct_0, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.75/0.93       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      (![X24 : $i]:
% 0.75/0.93         (~ (v1_xboole_0 @ (k2_struct_0 @ X24))
% 0.75/0.93          | ~ (l1_struct_0 @ X24)
% 0.75/0.93          | (v2_struct_0 @ X24))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.75/0.93        | (v2_struct_0 @ sk_B)
% 0.75/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.93  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['6', '7'])).
% 0.75/0.93  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('clc', [status(thm)], ['8', '9'])).
% 0.75/0.93  thf(t65_funct_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.93       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.75/0.93  thf('11', plain,
% 0.75/0.93      (![X5 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X5)
% 0.75/0.93          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.75/0.93          | ~ (v1_funct_1 @ X5)
% 0.75/0.93          | ~ (v1_relat_1 @ X5))),
% 0.75/0.93      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.75/0.93  thf(d3_struct_0, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('14', plain,
% 0.75/0.93      (((m1_subset_1 @ sk_C @ 
% 0.75/0.93         (k1_zfmisc_1 @ 
% 0.75/0.93          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.75/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['12', '13'])).
% 0.75/0.93  thf('15', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.75/0.93      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/0.93  thf('17', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.75/0.93      inference('demod', [status(thm)], ['16', '17'])).
% 0.75/0.93  thf(t35_funct_2, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.93       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.75/0.93         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.93           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.75/0.93             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.75/0.93  thf('19', plain,
% 0.75/0.93      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.93         (((X20) = (k1_xboole_0))
% 0.75/0.93          | ~ (v1_funct_1 @ X21)
% 0.75/0.93          | ~ (v1_funct_2 @ X21 @ X22 @ X20)
% 0.75/0.93          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 0.75/0.93          | ((k5_relat_1 @ X21 @ (k2_funct_1 @ X21)) = (k6_partfun1 @ X22))
% 0.75/0.93          | ~ (v2_funct_1 @ X21)
% 0.75/0.93          | ((k2_relset_1 @ X22 @ X20 @ X21) != (X20)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.75/0.93  thf(redefinition_k6_partfun1, axiom,
% 0.75/0.93    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.75/0.93  thf('20', plain, (![X12 : $i]: ((k6_partfun1 @ X12) = (k6_relat_1 @ X12))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.93         (((X20) = (k1_xboole_0))
% 0.75/0.93          | ~ (v1_funct_1 @ X21)
% 0.75/0.93          | ~ (v1_funct_2 @ X21 @ X22 @ X20)
% 0.75/0.93          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 0.75/0.93          | ((k5_relat_1 @ X21 @ (k2_funct_1 @ X21)) = (k6_relat_1 @ X22))
% 0.75/0.93          | ~ (v2_funct_1 @ X21)
% 0.75/0.93          | ((k2_relset_1 @ X22 @ X20 @ X21) != (X20)))),
% 0.75/0.93      inference('demod', [status(thm)], ['19', '20'])).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93          != (k2_relat_1 @ sk_C))
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.93        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.75/0.93            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.75/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['18', '21'])).
% 0.75/0.93  thf('23', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.93         = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.93          = (k2_struct_0 @ sk_B))
% 0.75/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.93  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.93         = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['25', '26'])).
% 0.75/0.93  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.93  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.93  thf('30', plain,
% 0.75/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93         = (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.75/0.93  thf('31', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('32', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.93  thf('33', plain,
% 0.75/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('34', plain,
% 0.75/0.93      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.75/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['32', '33'])).
% 0.75/0.93  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('36', plain,
% 0.75/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['34', '35'])).
% 0.75/0.93  thf('37', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['36', '37'])).
% 0.75/0.93  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('40', plain,
% 0.75/0.93      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.75/0.93        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.75/0.93            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.93        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.75/0.93      inference('demod', [status(thm)], ['22', '30', '31', '38', '39'])).
% 0.75/0.93  thf('41', plain,
% 0.75/0.93      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.75/0.93        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.75/0.93            = (k6_relat_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['40'])).
% 0.75/0.93  thf(t58_funct_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.93       ( ( v2_funct_1 @ A ) =>
% 0.75/0.93         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.75/0.93             ( k1_relat_1 @ A ) ) & 
% 0.75/0.93           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.75/0.93             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.75/0.93  thf('42', plain,
% 0.75/0.93      (![X4 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X4)
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ (k2_funct_1 @ X4)))
% 0.75/0.93              = (k1_relat_1 @ X4))
% 0.75/0.93          | ~ (v1_funct_1 @ X4)
% 0.75/0.93          | ~ (v1_relat_1 @ X4))),
% 0.75/0.93      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.75/0.93  thf('43', plain,
% 0.75/0.93      ((((k2_relat_1 @ (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.93          = (k1_relat_1 @ sk_C))
% 0.75/0.93        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.75/0.93        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.93      inference('sup+', [status(thm)], ['41', '42'])).
% 0.75/0.93  thf(t71_relat_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.75/0.93       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.75/0.93  thf('44', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/0.93  thf('45', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(cc1_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( v1_relat_1 @ C ) ))).
% 0.75/0.93  thf('46', plain,
% 0.75/0.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.75/0.93         ((v1_relat_1 @ X6)
% 0.75/0.93          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.75/0.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.93  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.93  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('49', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('50', plain,
% 0.75/0.93      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.75/0.93        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.75/0.93      inference('demod', [status(thm)], ['43', '44', '47', '48', '49'])).
% 0.75/0.93  thf(fc6_funct_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.75/0.93       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.75/0.93         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.75/0.93         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.75/0.93  thf('51', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v2_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('52', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.75/0.93      inference('demod', [status(thm)], ['16', '17'])).
% 0.75/0.93  thf(t31_funct_2, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.93       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.75/0.93         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.75/0.93           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.75/0.93           ( m1_subset_1 @
% 0.75/0.93             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.75/0.93  thf('53', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X17)
% 0.75/0.93          | ((k2_relset_1 @ X19 @ X18 @ X17) != (X18))
% 0.75/0.93          | (m1_subset_1 @ (k2_funct_1 @ X17) @ 
% 0.75/0.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.75/0.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18)))
% 0.75/0.93          | ~ (v1_funct_2 @ X17 @ X19 @ X18)
% 0.75/0.93          | ~ (v1_funct_1 @ X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.93  thf('54', plain,
% 0.75/0.93      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.75/0.93        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.93           (k1_zfmisc_1 @ 
% 0.75/0.93            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.75/0.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93            != (k2_relat_1 @ sk_C))
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.93      inference('sup-', [status(thm)], ['52', '53'])).
% 0.75/0.93  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('56', plain,
% 0.75/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['36', '37'])).
% 0.75/0.93  thf('57', plain,
% 0.75/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93         = (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.75/0.93  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('59', plain,
% 0.75/0.93      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.93         (k1_zfmisc_1 @ 
% 0.75/0.93          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.75/0.93        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.75/0.93      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.75/0.93  thf('60', plain,
% 0.75/0.93      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['59'])).
% 0.75/0.93  thf(d4_tops_2, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.93       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.75/0.93         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.75/0.93  thf('61', plain,
% 0.75/0.93      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.75/0.93         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.75/0.93          | ~ (v2_funct_1 @ X27)
% 0.75/0.93          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.75/0.93          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.75/0.93          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.75/0.93          | ~ (v1_funct_1 @ X27))),
% 0.75/0.93      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.75/0.93  thf('62', plain,
% 0.75/0.93      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.93        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.75/0.93             (u1_struct_0 @ sk_A))
% 0.75/0.93        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.93        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.93        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.75/0.93  thf('63', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.93  thf('64', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('65', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X17)
% 0.75/0.93          | ((k2_relset_1 @ X19 @ X18 @ X17) != (X18))
% 0.75/0.93          | (v1_funct_1 @ (k2_funct_1 @ X17))
% 0.75/0.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18)))
% 0.75/0.93          | ~ (v1_funct_2 @ X17 @ X19 @ X18)
% 0.75/0.93          | ~ (v1_funct_1 @ X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.93  thf('66', plain,
% 0.75/0.93      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.93        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.93            != (u1_struct_0 @ sk_B))
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.93      inference('sup-', [status(thm)], ['64', '65'])).
% 0.75/0.93  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('68', plain,
% 0.75/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('69', plain,
% 0.75/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.93         = (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.93  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('71', plain,
% 0.75/0.93      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.93        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.75/0.93      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.75/0.93  thf('72', plain,
% 0.75/0.93      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.75/0.93        | ~ (l1_struct_0 @ sk_B)
% 0.75/0.93        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['63', '71'])).
% 0.75/0.93  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.93  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('75', plain,
% 0.75/0.93      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.75/0.93        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.93      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.75/0.93  thf('76', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.93      inference('simplify', [status(thm)], ['75'])).
% 0.75/0.93  thf('77', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.75/0.93      inference('demod', [status(thm)], ['16', '17'])).
% 0.75/0.93  thf('78', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X17)
% 0.75/0.93          | ((k2_relset_1 @ X19 @ X18 @ X17) != (X18))
% 0.75/0.93          | (v1_funct_2 @ (k2_funct_1 @ X17) @ X18 @ X19)
% 0.75/0.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18)))
% 0.75/0.93          | ~ (v1_funct_2 @ X17 @ X19 @ X18)
% 0.75/0.93          | ~ (v1_funct_1 @ X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.93  thf('79', plain,
% 0.75/0.93      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.75/0.93        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.75/0.93           (u1_struct_0 @ sk_A))
% 0.75/0.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93            != (k2_relat_1 @ sk_C))
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.93      inference('sup-', [status(thm)], ['77', '78'])).
% 0.75/0.93  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('81', plain,
% 0.75/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['36', '37'])).
% 0.75/0.93  thf('82', plain,
% 0.75/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93         = (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.75/0.93  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('84', plain,
% 0.75/0.93      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.75/0.93         (u1_struct_0 @ sk_A))
% 0.75/0.93        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.75/0.93      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.75/0.93  thf('85', plain,
% 0.75/0.93      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.75/0.93        (u1_struct_0 @ sk_A))),
% 0.75/0.93      inference('simplify', [status(thm)], ['84'])).
% 0.75/0.93  thf('86', plain,
% 0.75/0.93      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['59'])).
% 0.75/0.93  thf('87', plain,
% 0.75/0.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.93         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.75/0.93          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.93  thf('88', plain,
% 0.75/0.93      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['86', '87'])).
% 0.75/0.93  thf('89', plain,
% 0.75/0.93      (![X4 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X4)
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ (k2_funct_1 @ X4)))
% 0.75/0.93              = (k1_relat_1 @ X4))
% 0.75/0.93          | ~ (v1_funct_1 @ X4)
% 0.75/0.93          | ~ (v1_relat_1 @ X4))),
% 0.75/0.93      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.75/0.93  thf('90', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v2_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('91', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.93      inference('simplify', [status(thm)], ['75'])).
% 0.75/0.93  thf('92', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('93', plain,
% 0.75/0.93      (![X5 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X5)
% 0.75/0.93          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.75/0.93          | ~ (v1_funct_1 @ X5)
% 0.75/0.93          | ~ (v1_relat_1 @ X5))),
% 0.75/0.93      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.75/0.93  thf('94', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v2_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('95', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('96', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('97', plain,
% 0.75/0.93      (![X5 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X5)
% 0.75/0.93          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.75/0.93          | ~ (v1_funct_1 @ X5)
% 0.75/0.93          | ~ (v1_relat_1 @ X5))),
% 0.75/0.93      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.75/0.93  thf('98', plain,
% 0.75/0.93      (![X4 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X4)
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ (k2_funct_1 @ X4)))
% 0.75/0.93              = (k1_relat_1 @ X4))
% 0.75/0.93          | ~ (v1_funct_1 @ X4)
% 0.75/0.93          | ~ (v1_relat_1 @ X4))),
% 0.75/0.93      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.75/0.93  thf('99', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['97', '98'])).
% 0.75/0.93  thf('100', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.75/0.93              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['96', '99'])).
% 0.75/0.93  thf('101', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['100'])).
% 0.75/0.93  thf('102', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.75/0.93              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['95', '101'])).
% 0.75/0.93  thf('103', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['102'])).
% 0.75/0.93  thf('104', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.75/0.93              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['94', '103'])).
% 0.75/0.93  thf('105', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['104'])).
% 0.75/0.93  thf('106', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['93', '105'])).
% 0.75/0.93  thf('107', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['92', '106'])).
% 0.75/0.93  thf('108', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['107'])).
% 0.75/0.93  thf('109', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.93        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['91', '108'])).
% 0.75/0.93  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.93  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('113', plain,
% 0.75/0.93      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.93        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.75/0.93      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.75/0.93  thf('114', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.93        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['90', '113'])).
% 0.75/0.93  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.93  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('118', plain,
% 0.75/0.93      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 0.75/0.93         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.93      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 0.75/0.93  thf('119', plain,
% 0.75/0.93      ((((k1_relat_1 @ sk_C)
% 0.75/0.93          = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.75/0.93        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.93      inference('sup+', [status(thm)], ['89', '118'])).
% 0.75/0.93  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.93  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('122', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('123', plain,
% 0.75/0.93      (((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.93      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.75/0.93  thf('124', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v2_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('125', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('126', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['107'])).
% 0.75/0.93  thf('127', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['125', '126'])).
% 0.75/0.93  thf('128', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['127'])).
% 0.75/0.93  thf('129', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['124', '128'])).
% 0.75/0.93  thf('130', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['129'])).
% 0.75/0.93  thf('131', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v2_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('132', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('133', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('134', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['129'])).
% 0.75/0.93  thf('135', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v2_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('136', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('137', plain,
% 0.75/0.93      (![X2 : $i]:
% 0.75/0.93         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.75/0.93          | ~ (v2_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_funct_1 @ X2)
% 0.75/0.93          | ~ (v1_relat_1 @ X2))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.93  thf('138', plain,
% 0.75/0.93      (![X5 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X5)
% 0.75/0.93          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.75/0.93          | ~ (v1_funct_1 @ X5)
% 0.75/0.93          | ~ (v1_relat_1 @ X5))),
% 0.75/0.93      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.75/0.93  thf(t55_funct_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.93       ( ( v2_funct_1 @ A ) =>
% 0.75/0.93         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.75/0.93           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.75/0.93  thf('139', plain,
% 0.75/0.93      (![X3 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X3)
% 0.75/0.93          | ((k1_relat_1 @ X3) = (k2_relat_1 @ (k2_funct_1 @ X3)))
% 0.75/0.93          | ~ (v1_funct_1 @ X3)
% 0.75/0.93          | ~ (v1_relat_1 @ X3))),
% 0.75/0.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.75/0.93  thf('140', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['138', '139'])).
% 0.75/0.93  thf('141', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['137', '140'])).
% 0.75/0.93  thf('142', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['141'])).
% 0.75/0.93  thf('143', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['136', '142'])).
% 0.75/0.93  thf('144', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['143'])).
% 0.75/0.93  thf('145', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['135', '144'])).
% 0.75/0.93  thf('146', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['145'])).
% 0.75/0.93  thf('147', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['134', '146'])).
% 0.75/0.93  thf('148', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['133', '147'])).
% 0.75/0.93  thf('149', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['148'])).
% 0.75/0.93  thf('150', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['132', '149'])).
% 0.75/0.93  thf('151', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['150'])).
% 0.75/0.93  thf('152', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['131', '151'])).
% 0.75/0.93  thf('153', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0))),
% 0.75/0.93      inference('simplify', [status(thm)], ['152'])).
% 0.75/0.93  thf('154', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['130', '153'])).
% 0.75/0.93  thf('155', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.75/0.93              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['154'])).
% 0.75/0.93  thf('156', plain,
% 0.75/0.93      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.93        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.93      inference('sup+', [status(thm)], ['123', '155'])).
% 0.75/0.93  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.93  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('160', plain,
% 0.75/0.93      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.93      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 0.75/0.93  thf('161', plain,
% 0.75/0.93      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['88', '160'])).
% 0.75/0.93  thf('162', plain,
% 0.75/0.93      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.93        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.93        | ((k1_relat_1 @ sk_C) != (u1_struct_0 @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['62', '76', '85', '161'])).
% 0.75/0.93  thf('163', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.93        | ((k1_relat_1 @ sk_C) != (u1_struct_0 @ sk_A))
% 0.75/0.93        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['51', '162'])).
% 0.75/0.93  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.93  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('167', plain,
% 0.75/0.93      ((((k1_relat_1 @ sk_C) != (u1_struct_0 @ sk_A))
% 0.75/0.93        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.93      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 0.75/0.93  thf('168', plain,
% 0.75/0.93      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.75/0.93        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.75/0.93        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['50', '167'])).
% 0.75/0.93  thf('169', plain,
% 0.75/0.93      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.93        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['168'])).
% 0.75/0.93  thf('170', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.93  thf('171', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.93  thf('172', plain,
% 0.75/0.93      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.93          sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('173', plain,
% 0.75/0.93      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.93           sk_C)
% 0.75/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['171', '172'])).
% 0.75/0.93  thf('174', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('175', plain,
% 0.75/0.93      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.93          sk_C)),
% 0.75/0.93      inference('demod', [status(thm)], ['173', '174'])).
% 0.75/0.93  thf('176', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.93  thf('177', plain,
% 0.75/0.93      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.75/0.93          sk_C)),
% 0.75/0.93      inference('demod', [status(thm)], ['175', '176'])).
% 0.75/0.93  thf('178', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.75/0.93      inference('demod', [status(thm)], ['16', '17'])).
% 0.75/0.93  thf('179', plain,
% 0.75/0.93      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.75/0.93         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.75/0.93          | ~ (v2_funct_1 @ X27)
% 0.75/0.93          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.75/0.93          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.75/0.93          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.75/0.93          | ~ (v1_funct_1 @ X27))),
% 0.75/0.93      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.75/0.93  thf('180', plain,
% 0.75/0.93      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.75/0.93        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93            = (k2_funct_1 @ sk_C))
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93            != (k2_relat_1 @ sk_C)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['178', '179'])).
% 0.75/0.93  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('182', plain,
% 0.75/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['36', '37'])).
% 0.75/0.93  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('184', plain,
% 0.75/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93         = (k2_relat_1 @ sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.75/0.93  thf('185', plain,
% 0.75/0.93      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93          = (k2_funct_1 @ sk_C))
% 0.75/0.93        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.75/0.93      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 0.75/0.93  thf('186', plain,
% 0.75/0.93      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.75/0.93         = (k2_funct_1 @ sk_C))),
% 0.75/0.93      inference('simplify', [status(thm)], ['185'])).
% 0.75/0.93  thf('187', plain,
% 0.75/0.93      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93           (k2_funct_1 @ sk_C)) @ 
% 0.75/0.93          sk_C)),
% 0.75/0.93      inference('demod', [status(thm)], ['177', '186'])).
% 0.75/0.93  thf('188', plain,
% 0.75/0.93      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.93           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93            (k2_funct_1 @ sk_C)) @ 
% 0.75/0.93           sk_C)
% 0.75/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['170', '187'])).
% 0.75/0.93  thf('189', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.93  thf('190', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('191', plain,
% 0.75/0.93      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.93          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.93           (k2_funct_1 @ sk_C)) @ 
% 0.75/0.93          sk_C)),
% 0.75/0.93      inference('demod', [status(thm)], ['188', '189', '190'])).
% 0.75/0.93  thf('192', plain,
% 0.75/0.93      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.93           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 0.75/0.93        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['169', '191'])).
% 0.75/0.93  thf('193', plain,
% 0.75/0.93      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.93           sk_C)
% 0.75/0.93        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.93        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['11', '192'])).
% 0.75/0.93  thf('194', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('195', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_C @ 
% 0.75/0.93        (k1_zfmisc_1 @ 
% 0.75/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(reflexivity_r2_funct_2, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.93         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.75/0.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.93       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.75/0.93  thf('196', plain,
% 0.75/0.93      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.93         ((r2_funct_2 @ X13 @ X14 @ X15 @ X15)
% 0.75/0.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.75/0.93          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.75/0.93          | ~ (v1_funct_1 @ X15)
% 0.75/0.93          | ~ (v1_funct_1 @ X16)
% 0.75/0.93          | ~ (v1_funct_2 @ X16 @ X13 @ X14)
% 0.75/0.93          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.75/0.93      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.75/0.93  thf('197', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X0 @ 
% 0.75/0.93             (k1_zfmisc_1 @ 
% 0.75/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.75/0.93          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.93          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.93             sk_C))),
% 0.75/0.93      inference('sup-', [status(thm)], ['195', '196'])).
% 0.75/0.93  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('199', plain,
% 0.75/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('200', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X0 @ 
% 0.75/0.93             (k1_zfmisc_1 @ 
% 0.75/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.75/0.93          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.93             sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['197', '198', '199'])).
% 0.75/0.93  thf('201', plain,
% 0.75/0.93      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['194', '200'])).
% 0.75/0.93  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('203', plain,
% 0.75/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('204', plain,
% 0.75/0.93      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.75/0.93      inference('demod', [status(thm)], ['201', '202', '203'])).
% 0.75/0.93  thf('205', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.93  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('207', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('208', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.75/0.93      inference('demod', [status(thm)], ['193', '204', '205', '206', '207'])).
% 0.75/0.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.75/0.93  thf('209', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.93  thf('210', plain, ($false),
% 0.75/0.93      inference('demod', [status(thm)], ['10', '208', '209'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
