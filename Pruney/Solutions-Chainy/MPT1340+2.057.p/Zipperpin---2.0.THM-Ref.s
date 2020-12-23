%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dtg8hyGh97

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:16 EST 2020

% Result     : Theorem 29.89s
% Output     : Refutation 29.89s
% Verified   : 
% Statistics : Number of formulae       :  306 (3657 expanded)
%              Number of leaves         :   47 (1074 expanded)
%              Depth                    :   28
%              Number of atoms          : 2788 (82414 expanded)
%              Number of equality atoms :  177 (2606 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
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

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
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

thf('18',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( ( k5_relat_1 @ X32 @ ( k2_funct_1 @ X32 ) )
        = ( k6_partfun1 @ X33 ) )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X33 @ X31 @ X32 )
       != X31 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('24',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('36',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
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
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','36','37','48','49'])).

thf('51',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

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

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('53',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('55',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('58',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('62',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('63',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('69',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('71',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('75',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('76',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('80',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('81',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('82',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('84',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != X21 )
      | ( v1_partfun1 @ X22 @ X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('85',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v4_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
      | ( v1_partfun1 @ X22 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','95'])).

thf('97',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['79','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('105',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('106',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('109',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','56','69','78','106','107','108'])).

thf('110',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

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

thf('112',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('113',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('114',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('117',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('118',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('121',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119','120'])).

thf('122',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['110','122'])).

thf('124',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['11','124'])).

thf('126',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('134',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('135',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('143',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136','143'])).

thf('145',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('146',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['126','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('154',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('155',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['125','156','157','158','159'])).

thf('161',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('163',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('164',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('166',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('167',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('171',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('172',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','168','169','172','173'])).

thf('175',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['164','174'])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('177',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

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

thf('180',plain,(
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

thf('181',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('183',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('184',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('185',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('186',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('189',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187','188','189','190'])).

thf('192',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','191'])).

thf('193',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('194',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('198',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('199',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['181','182','196','199'])).

thf('201',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['163','200'])).

thf('202',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['162','201'])).

thf('203',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','155'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['202','203','204','205','206'])).

thf('208',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('210',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('211',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['209','214'])).

thf('216',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('219',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('220',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('222',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('224',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['220','221','224'])).

thf('226',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','155'])).

thf('227',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('229',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('230',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['217','227','228','229'])).

thf('231',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('232',plain,(
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

thf('233',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('236',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('238',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['233','234','235','236','237'])).

thf('239',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['230','239'])).

thf('241',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['208','240'])).

thf('242',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['161','241'])).

thf('243',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('245',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('246',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['244','250'])).

thf('252',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('254',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['243','254'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('256',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('257',plain,(
    $false ),
    inference(demod,[status(thm)],['10','255','256'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dtg8hyGh97
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.89/30.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 29.89/30.10  % Solved by: fo/fo7.sh
% 29.89/30.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.89/30.10  % done 498 iterations in 29.638s
% 29.89/30.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 29.89/30.10  % SZS output start Refutation
% 29.89/30.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 29.89/30.10  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 29.89/30.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 29.89/30.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 29.89/30.10  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 29.89/30.10  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 29.89/30.10  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 29.89/30.10  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 29.89/30.10  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 29.89/30.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 29.89/30.10  thf(sk_C_type, type, sk_C: $i).
% 29.89/30.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 29.89/30.10  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 29.89/30.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 29.89/30.10  thf(sk_B_type, type, sk_B: $i).
% 29.89/30.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.89/30.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 29.89/30.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 29.89/30.10  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 29.89/30.10  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 29.89/30.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 29.89/30.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 29.89/30.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 29.89/30.10  thf(sk_A_type, type, sk_A: $i).
% 29.89/30.10  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 29.89/30.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 29.89/30.10  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 29.89/30.10  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 29.89/30.10  thf(t64_tops_2, conjecture,
% 29.89/30.10    (![A:$i]:
% 29.89/30.10     ( ( l1_struct_0 @ A ) =>
% 29.89/30.10       ( ![B:$i]:
% 29.89/30.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 29.89/30.10           ( ![C:$i]:
% 29.89/30.10             ( ( ( v1_funct_1 @ C ) & 
% 29.89/30.10                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 29.89/30.10                 ( m1_subset_1 @
% 29.89/30.10                   C @ 
% 29.89/30.10                   ( k1_zfmisc_1 @
% 29.89/30.10                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 29.89/30.10               ( ( ( ( k2_relset_1 @
% 29.89/30.10                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 29.89/30.10                     ( k2_struct_0 @ B ) ) & 
% 29.89/30.10                   ( v2_funct_1 @ C ) ) =>
% 29.89/30.10                 ( r2_funct_2 @
% 29.89/30.10                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 29.89/30.10                   ( k2_tops_2 @
% 29.89/30.10                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 29.89/30.10                     ( k2_tops_2 @
% 29.89/30.10                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 29.89/30.10                   C ) ) ) ) ) ) ))).
% 29.89/30.10  thf(zf_stmt_0, negated_conjecture,
% 29.89/30.10    (~( ![A:$i]:
% 29.89/30.10        ( ( l1_struct_0 @ A ) =>
% 29.89/30.10          ( ![B:$i]:
% 29.89/30.10            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 29.89/30.10              ( ![C:$i]:
% 29.89/30.10                ( ( ( v1_funct_1 @ C ) & 
% 29.89/30.10                    ( v1_funct_2 @
% 29.89/30.10                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 29.89/30.10                    ( m1_subset_1 @
% 29.89/30.10                      C @ 
% 29.89/30.10                      ( k1_zfmisc_1 @
% 29.89/30.10                        ( k2_zfmisc_1 @
% 29.89/30.10                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 29.89/30.10                  ( ( ( ( k2_relset_1 @
% 29.89/30.10                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 29.89/30.10                        ( k2_struct_0 @ B ) ) & 
% 29.89/30.10                      ( v2_funct_1 @ C ) ) =>
% 29.89/30.10                    ( r2_funct_2 @
% 29.89/30.10                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 29.89/30.10                      ( k2_tops_2 @
% 29.89/30.10                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 29.89/30.10                        ( k2_tops_2 @
% 29.89/30.10                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 29.89/30.10                      C ) ) ) ) ) ) ) )),
% 29.89/30.10    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 29.89/30.10  thf('0', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf(redefinition_k2_relset_1, axiom,
% 29.89/30.10    (![A:$i,B:$i,C:$i]:
% 29.89/30.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.89/30.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 29.89/30.10  thf('1', plain,
% 29.89/30.10      (![X15 : $i, X16 : $i, X17 : $i]:
% 29.89/30.10         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 29.89/30.10          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 29.89/30.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 29.89/30.10  thf('2', plain,
% 29.89/30.10      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 29.89/30.10         = (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['0', '1'])).
% 29.89/30.10  thf('3', plain,
% 29.89/30.10      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 29.89/30.10         = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.10  thf(fc5_struct_0, axiom,
% 29.89/30.10    (![A:$i]:
% 29.89/30.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 29.89/30.10       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 29.89/30.10  thf('5', plain,
% 29.89/30.10      (![X35 : $i]:
% 29.89/30.10         (~ (v1_xboole_0 @ (k2_struct_0 @ X35))
% 29.89/30.10          | ~ (l1_struct_0 @ X35)
% 29.89/30.10          | (v2_struct_0 @ X35))),
% 29.89/30.10      inference('cnf', [status(esa)], [fc5_struct_0])).
% 29.89/30.10  thf('6', plain,
% 29.89/30.10      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 29.89/30.10        | (v2_struct_0 @ sk_B)
% 29.89/30.10        | ~ (l1_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup-', [status(thm)], ['4', '5'])).
% 29.89/30.10  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('8', plain,
% 29.89/30.10      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 29.89/30.10      inference('demod', [status(thm)], ['6', '7'])).
% 29.89/30.10  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('clc', [status(thm)], ['8', '9'])).
% 29.89/30.10  thf(t55_funct_1, axiom,
% 29.89/30.10    (![A:$i]:
% 29.89/30.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.89/30.10       ( ( v2_funct_1 @ A ) =>
% 29.89/30.10         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 29.89/30.10           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 29.89/30.10  thf('11', plain,
% 29.89/30.10      (![X9 : $i]:
% 29.89/30.10         (~ (v2_funct_1 @ X9)
% 29.89/30.10          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 29.89/30.10          | ~ (v1_funct_1 @ X9)
% 29.89/30.10          | ~ (v1_relat_1 @ X9))),
% 29.89/30.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.89/30.10  thf(d3_struct_0, axiom,
% 29.89/30.10    (![A:$i]:
% 29.89/30.10     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 29.89/30.10  thf('12', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('13', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('14', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('15', plain,
% 29.89/30.10      (((m1_subset_1 @ sk_C @ 
% 29.89/30.10         (k1_zfmisc_1 @ 
% 29.89/30.10          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 29.89/30.10        | ~ (l1_struct_0 @ sk_A))),
% 29.89/30.10      inference('sup+', [status(thm)], ['13', '14'])).
% 29.89/30.10  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('17', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.10      inference('demod', [status(thm)], ['15', '16'])).
% 29.89/30.10  thf('18', plain,
% 29.89/30.10      (((m1_subset_1 @ sk_C @ 
% 29.89/30.10         (k1_zfmisc_1 @ 
% 29.89/30.10          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 29.89/30.10        | ~ (l1_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['12', '17'])).
% 29.89/30.10  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('20', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 29.89/30.10      inference('demod', [status(thm)], ['18', '19'])).
% 29.89/30.10  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.10  thf('22', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 29.89/30.10      inference('demod', [status(thm)], ['20', '21'])).
% 29.89/30.10  thf(t35_funct_2, axiom,
% 29.89/30.10    (![A:$i,B:$i,C:$i]:
% 29.89/30.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 29.89/30.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.89/30.10       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 29.89/30.10         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.89/30.10           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 29.89/30.10             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 29.89/30.10  thf('23', plain,
% 29.89/30.10      (![X31 : $i, X32 : $i, X33 : $i]:
% 29.89/30.10         (((X31) = (k1_xboole_0))
% 29.89/30.10          | ~ (v1_funct_1 @ X32)
% 29.89/30.10          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 29.89/30.10          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 29.89/30.10          | ((k5_relat_1 @ X32 @ (k2_funct_1 @ X32)) = (k6_partfun1 @ X33))
% 29.89/30.10          | ~ (v2_funct_1 @ X32)
% 29.89/30.10          | ((k2_relset_1 @ X33 @ X31 @ X32) != (X31)))),
% 29.89/30.10      inference('cnf', [status(esa)], [t35_funct_2])).
% 29.89/30.10  thf('24', plain,
% 29.89/30.10      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.10          != (k2_relat_1 @ sk_C))
% 29.89/30.10        | ~ (v2_funct_1 @ sk_C)
% 29.89/30.10        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 29.89/30.10            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 29.89/30.10        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 29.89/30.10        | ~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.10      inference('sup-', [status(thm)], ['22', '23'])).
% 29.89/30.10  thf('25', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('26', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('27', plain,
% 29.89/30.10      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 29.89/30.10         = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('28', plain,
% 29.89/30.10      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 29.89/30.10          = (k2_struct_0 @ sk_B))
% 29.89/30.10        | ~ (l1_struct_0 @ sk_A))),
% 29.89/30.10      inference('sup+', [status(thm)], ['26', '27'])).
% 29.89/30.10  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('30', plain,
% 29.89/30.10      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 29.89/30.10         = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('demod', [status(thm)], ['28', '29'])).
% 29.89/30.10  thf('31', plain,
% 29.89/30.10      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 29.89/30.10          = (k2_struct_0 @ sk_B))
% 29.89/30.10        | ~ (l1_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['25', '30'])).
% 29.89/30.10  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('33', plain,
% 29.89/30.10      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 29.89/30.10         = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('demod', [status(thm)], ['31', '32'])).
% 29.89/30.10  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.10  thf('35', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.10  thf('36', plain,
% 29.89/30.10      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.10         = (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['33', '34', '35'])).
% 29.89/30.10  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('38', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('39', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('40', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('41', plain,
% 29.89/30.10      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 29.89/30.10        | ~ (l1_struct_0 @ sk_A))),
% 29.89/30.10      inference('sup+', [status(thm)], ['39', '40'])).
% 29.89/30.10  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('43', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 29.89/30.10      inference('demod', [status(thm)], ['41', '42'])).
% 29.89/30.10  thf('44', plain,
% 29.89/30.10      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 29.89/30.10        | ~ (l1_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['38', '43'])).
% 29.89/30.10  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('46', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('demod', [status(thm)], ['44', '45'])).
% 29.89/30.10  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.10  thf('48', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['46', '47'])).
% 29.89/30.10  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('50', plain,
% 29.89/30.10      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 29.89/30.10        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 29.89/30.10            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.10      inference('demod', [status(thm)], ['24', '36', '37', '48', '49'])).
% 29.89/30.10  thf('51', plain,
% 29.89/30.10      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 29.89/30.10            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 29.89/30.10      inference('simplify', [status(thm)], ['50'])).
% 29.89/30.10  thf(t48_funct_1, axiom,
% 29.89/30.10    (![A:$i]:
% 29.89/30.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.89/30.10       ( ![B:$i]:
% 29.89/30.10         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 29.89/30.10           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 29.89/30.10               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 29.89/30.10             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 29.89/30.10  thf('52', plain,
% 29.89/30.10      (![X7 : $i, X8 : $i]:
% 29.89/30.10         (~ (v1_relat_1 @ X7)
% 29.89/30.10          | ~ (v1_funct_1 @ X7)
% 29.89/30.10          | (v2_funct_1 @ X8)
% 29.89/30.10          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 29.89/30.10          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 29.89/30.10          | ~ (v1_funct_1 @ X8)
% 29.89/30.10          | ~ (v1_relat_1 @ X8))),
% 29.89/30.10      inference('cnf', [status(esa)], [t48_funct_1])).
% 29.89/30.10  thf('53', plain,
% 29.89/30.10      ((~ (v2_funct_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.10        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v1_relat_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['51', '52'])).
% 29.89/30.10  thf(fc4_funct_1, axiom,
% 29.89/30.10    (![A:$i]:
% 29.89/30.10     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 29.89/30.10       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 29.89/30.10  thf('54', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 29.89/30.10      inference('cnf', [status(esa)], [fc4_funct_1])).
% 29.89/30.10  thf(redefinition_k6_partfun1, axiom,
% 29.89/30.10    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 29.89/30.10  thf('55', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 29.89/30.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 29.89/30.10  thf('56', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 29.89/30.10      inference('demod', [status(thm)], ['54', '55'])).
% 29.89/30.10  thf('57', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 29.89/30.10      inference('demod', [status(thm)], ['20', '21'])).
% 29.89/30.10  thf(t31_funct_2, axiom,
% 29.89/30.10    (![A:$i,B:$i,C:$i]:
% 29.89/30.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 29.89/30.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.89/30.10       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 29.89/30.10         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 29.89/30.10           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 29.89/30.10           ( m1_subset_1 @
% 29.89/30.10             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 29.89/30.10  thf('58', plain,
% 29.89/30.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.89/30.10         (~ (v2_funct_1 @ X28)
% 29.89/30.10          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 29.89/30.10          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 29.89/30.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 29.89/30.10          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 29.89/30.10          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 29.89/30.10          | ~ (v1_funct_1 @ X28))),
% 29.89/30.10      inference('cnf', [status(esa)], [t31_funct_2])).
% 29.89/30.10  thf('59', plain,
% 29.89/30.10      ((~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 29.89/30.10        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10           (k1_zfmisc_1 @ 
% 29.89/30.10            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 29.89/30.10        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.10            != (k2_relat_1 @ sk_C))
% 29.89/30.10        | ~ (v2_funct_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['57', '58'])).
% 29.89/30.10  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('61', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['46', '47'])).
% 29.89/30.10  thf('62', plain,
% 29.89/30.10      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.10         = (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['33', '34', '35'])).
% 29.89/30.10  thf('63', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('64', plain,
% 29.89/30.10      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10         (k1_zfmisc_1 @ 
% 29.89/30.10          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 29.89/30.10      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 29.89/30.10  thf('65', plain,
% 29.89/30.10      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 29.89/30.10      inference('simplify', [status(thm)], ['64'])).
% 29.89/30.10  thf(cc2_relat_1, axiom,
% 29.89/30.10    (![A:$i]:
% 29.89/30.10     ( ( v1_relat_1 @ A ) =>
% 29.89/30.10       ( ![B:$i]:
% 29.89/30.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 29.89/30.10  thf('66', plain,
% 29.89/30.10      (![X0 : $i, X1 : $i]:
% 29.89/30.10         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 29.89/30.10          | (v1_relat_1 @ X0)
% 29.89/30.10          | ~ (v1_relat_1 @ X1))),
% 29.89/30.10      inference('cnf', [status(esa)], [cc2_relat_1])).
% 29.89/30.10  thf('67', plain,
% 29.89/30.10      ((~ (v1_relat_1 @ 
% 29.89/30.10           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A)))
% 29.89/30.10        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 29.89/30.10      inference('sup-', [status(thm)], ['65', '66'])).
% 29.89/30.10  thf(fc6_relat_1, axiom,
% 29.89/30.10    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 29.89/30.10  thf('68', plain,
% 29.89/30.10      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 29.89/30.10      inference('cnf', [status(esa)], [fc6_relat_1])).
% 29.89/30.10  thf('69', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['67', '68'])).
% 29.89/30.10  thf('70', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 29.89/30.10      inference('demod', [status(thm)], ['20', '21'])).
% 29.89/30.10  thf('71', plain,
% 29.89/30.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.89/30.10         (~ (v2_funct_1 @ X28)
% 29.89/30.10          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 29.89/30.10          | (v1_funct_1 @ (k2_funct_1 @ X28))
% 29.89/30.10          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 29.89/30.10          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 29.89/30.10          | ~ (v1_funct_1 @ X28))),
% 29.89/30.10      inference('cnf', [status(esa)], [t31_funct_2])).
% 29.89/30.10  thf('72', plain,
% 29.89/30.10      ((~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 29.89/30.10        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.10            != (k2_relat_1 @ sk_C))
% 29.89/30.10        | ~ (v2_funct_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['70', '71'])).
% 29.89/30.10  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('74', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['46', '47'])).
% 29.89/30.10  thf('75', plain,
% 29.89/30.10      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.10         = (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['33', '34', '35'])).
% 29.89/30.10  thf('76', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('77', plain,
% 29.89/30.10      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 29.89/30.10      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 29.89/30.10  thf('78', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 29.89/30.10      inference('simplify', [status(thm)], ['77'])).
% 29.89/30.10  thf('79', plain,
% 29.89/30.10      (![X9 : $i]:
% 29.89/30.10         (~ (v2_funct_1 @ X9)
% 29.89/30.10          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 29.89/30.10          | ~ (v1_funct_1 @ X9)
% 29.89/30.10          | ~ (v1_relat_1 @ X9))),
% 29.89/30.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.89/30.10  thf('80', plain,
% 29.89/30.10      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 29.89/30.10      inference('simplify', [status(thm)], ['64'])).
% 29.89/30.10  thf(cc2_relset_1, axiom,
% 29.89/30.10    (![A:$i,B:$i,C:$i]:
% 29.89/30.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.89/30.10       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 29.89/30.10  thf('81', plain,
% 29.89/30.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 29.89/30.10         ((v4_relat_1 @ X12 @ X13)
% 29.89/30.10          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 29.89/30.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 29.89/30.10  thf('82', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['80', '81'])).
% 29.89/30.10  thf('83', plain,
% 29.89/30.10      (![X9 : $i]:
% 29.89/30.10         (~ (v2_funct_1 @ X9)
% 29.89/30.10          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 29.89/30.10          | ~ (v1_funct_1 @ X9)
% 29.89/30.10          | ~ (v1_relat_1 @ X9))),
% 29.89/30.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.89/30.10  thf(d4_partfun1, axiom,
% 29.89/30.10    (![A:$i,B:$i]:
% 29.89/30.10     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 29.89/30.10       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 29.89/30.10  thf('84', plain,
% 29.89/30.10      (![X21 : $i, X22 : $i]:
% 29.89/30.10         (((k1_relat_1 @ X22) != (X21))
% 29.89/30.10          | (v1_partfun1 @ X22 @ X21)
% 29.89/30.10          | ~ (v4_relat_1 @ X22 @ X21)
% 29.89/30.10          | ~ (v1_relat_1 @ X22))),
% 29.89/30.10      inference('cnf', [status(esa)], [d4_partfun1])).
% 29.89/30.10  thf('85', plain,
% 29.89/30.10      (![X22 : $i]:
% 29.89/30.10         (~ (v1_relat_1 @ X22)
% 29.89/30.10          | ~ (v4_relat_1 @ X22 @ (k1_relat_1 @ X22))
% 29.89/30.10          | (v1_partfun1 @ X22 @ (k1_relat_1 @ X22)))),
% 29.89/30.10      inference('simplify', [status(thm)], ['84'])).
% 29.89/30.10  thf('86', plain,
% 29.89/30.10      (![X0 : $i]:
% 29.89/30.10         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 29.89/30.10          | ~ (v1_relat_1 @ X0)
% 29.89/30.10          | ~ (v1_funct_1 @ X0)
% 29.89/30.10          | ~ (v2_funct_1 @ X0)
% 29.89/30.10          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 29.89/30.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 29.89/30.10      inference('sup-', [status(thm)], ['83', '85'])).
% 29.89/30.10  thf('87', plain,
% 29.89/30.10      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.10        | ~ (v2_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v1_relat_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['82', '86'])).
% 29.89/30.10  thf('88', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['67', '68'])).
% 29.89/30.10  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('91', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('92', plain,
% 29.89/30.10      (![X0 : $i, X1 : $i]:
% 29.89/30.10         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 29.89/30.10          | (v1_relat_1 @ X0)
% 29.89/30.10          | ~ (v1_relat_1 @ X1))),
% 29.89/30.10      inference('cnf', [status(esa)], [cc2_relat_1])).
% 29.89/30.10  thf('93', plain,
% 29.89/30.10      ((~ (v1_relat_1 @ 
% 29.89/30.10           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 29.89/30.10        | (v1_relat_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['91', '92'])).
% 29.89/30.10  thf('94', plain,
% 29.89/30.10      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 29.89/30.10      inference('cnf', [status(esa)], [fc6_relat_1])).
% 29.89/30.10  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 29.89/30.10      inference('demod', [status(thm)], ['93', '94'])).
% 29.89/30.10  thf('96', plain,
% 29.89/30.10      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 29.89/30.10      inference('demod', [status(thm)], ['87', '88', '89', '90', '95'])).
% 29.89/30.10  thf('97', plain,
% 29.89/30.10      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 29.89/30.10        | ~ (v1_relat_1 @ sk_C)
% 29.89/30.10        | ~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v2_funct_1 @ sk_C))),
% 29.89/30.10      inference('sup+', [status(thm)], ['79', '96'])).
% 29.89/30.10  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 29.89/30.10      inference('demod', [status(thm)], ['93', '94'])).
% 29.89/30.10  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('101', plain,
% 29.89/30.10      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 29.89/30.10  thf('102', plain,
% 29.89/30.10      (![X21 : $i, X22 : $i]:
% 29.89/30.10         (~ (v1_partfun1 @ X22 @ X21)
% 29.89/30.10          | ((k1_relat_1 @ X22) = (X21))
% 29.89/30.10          | ~ (v4_relat_1 @ X22 @ X21)
% 29.89/30.10          | ~ (v1_relat_1 @ X22))),
% 29.89/30.10      inference('cnf', [status(esa)], [d4_partfun1])).
% 29.89/30.10  thf('103', plain,
% 29.89/30.10      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 29.89/30.10        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 29.89/30.10      inference('sup-', [status(thm)], ['101', '102'])).
% 29.89/30.10  thf('104', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['67', '68'])).
% 29.89/30.10  thf('105', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['80', '81'])).
% 29.89/30.10  thf('106', plain,
% 29.89/30.10      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['103', '104', '105'])).
% 29.89/30.10  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 29.89/30.10      inference('demod', [status(thm)], ['93', '94'])).
% 29.89/30.10  thf('109', plain,
% 29.89/30.10      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 29.89/30.10        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 29.89/30.10      inference('demod', [status(thm)],
% 29.89/30.10                ['53', '56', '69', '78', '106', '107', '108'])).
% 29.89/30.10  thf('110', plain,
% 29.89/30.10      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.10      inference('simplify', [status(thm)], ['109'])).
% 29.89/30.10  thf('111', plain,
% 29.89/30.10      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 29.89/30.10            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 29.89/30.10      inference('simplify', [status(thm)], ['50'])).
% 29.89/30.10  thf(t64_funct_1, axiom,
% 29.89/30.10    (![A:$i]:
% 29.89/30.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.89/30.10       ( ![B:$i]:
% 29.89/30.10         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 29.89/30.10           ( ( ( v2_funct_1 @ A ) & 
% 29.89/30.10               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 29.89/30.10               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 29.89/30.10             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 29.89/30.10  thf('112', plain,
% 29.89/30.10      (![X10 : $i, X11 : $i]:
% 29.89/30.10         (~ (v1_relat_1 @ X10)
% 29.89/30.10          | ~ (v1_funct_1 @ X10)
% 29.89/30.10          | ((X10) = (k2_funct_1 @ X11))
% 29.89/30.10          | ((k5_relat_1 @ X10 @ X11) != (k6_relat_1 @ (k2_relat_1 @ X11)))
% 29.89/30.10          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 29.89/30.10          | ~ (v2_funct_1 @ X11)
% 29.89/30.10          | ~ (v1_funct_1 @ X11)
% 29.89/30.10          | ~ (v1_relat_1 @ X11))),
% 29.89/30.10      inference('cnf', [status(esa)], [t64_funct_1])).
% 29.89/30.10  thf('113', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 29.89/30.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 29.89/30.10  thf('114', plain,
% 29.89/30.10      (![X10 : $i, X11 : $i]:
% 29.89/30.10         (~ (v1_relat_1 @ X10)
% 29.89/30.10          | ~ (v1_funct_1 @ X10)
% 29.89/30.10          | ((X10) = (k2_funct_1 @ X11))
% 29.89/30.10          | ((k5_relat_1 @ X10 @ X11) != (k6_partfun1 @ (k2_relat_1 @ X11)))
% 29.89/30.10          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 29.89/30.10          | ~ (v2_funct_1 @ X11)
% 29.89/30.10          | ~ (v1_funct_1 @ X11)
% 29.89/30.10          | ~ (v1_relat_1 @ X11))),
% 29.89/30.10      inference('demod', [status(thm)], ['112', '113'])).
% 29.89/30.10  thf('115', plain,
% 29.89/30.10      ((((k6_partfun1 @ (k2_struct_0 @ sk_A))
% 29.89/30.10          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.10        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.10        | ~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v1_relat_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['111', '114'])).
% 29.89/30.10  thf('116', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['67', '68'])).
% 29.89/30.10  thf('117', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 29.89/30.10      inference('simplify', [status(thm)], ['77'])).
% 29.89/30.10  thf('118', plain,
% 29.89/30.10      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['103', '104', '105'])).
% 29.89/30.10  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 29.89/30.10      inference('demod', [status(thm)], ['93', '94'])).
% 29.89/30.10  thf('121', plain,
% 29.89/30.10      ((((k6_partfun1 @ (k2_struct_0 @ sk_A))
% 29.89/30.10          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 29.89/30.10        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.89/30.10      inference('demod', [status(thm)],
% 29.89/30.10                ['115', '116', '117', '118', '119', '120'])).
% 29.89/30.10  thf('122', plain,
% 29.89/30.10      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.10        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ((k6_partfun1 @ (k2_struct_0 @ sk_A))
% 29.89/30.10            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 29.89/30.10      inference('simplify', [status(thm)], ['121'])).
% 29.89/30.10  thf('123', plain,
% 29.89/30.10      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ((k6_partfun1 @ (k2_struct_0 @ sk_A))
% 29.89/30.10            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.89/30.10      inference('sup-', [status(thm)], ['110', '122'])).
% 29.89/30.10  thf('124', plain,
% 29.89/30.10      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.10        | ((k6_partfun1 @ (k2_struct_0 @ sk_A))
% 29.89/30.10            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.10      inference('simplify', [status(thm)], ['123'])).
% 29.89/30.10  thf('125', plain,
% 29.89/30.10      ((((k6_partfun1 @ (k2_struct_0 @ sk_A))
% 29.89/30.10          != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 29.89/30.10        | ~ (v1_relat_1 @ sk_C)
% 29.89/30.10        | ~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v2_funct_1 @ sk_C)
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.89/30.10      inference('sup-', [status(thm)], ['11', '124'])).
% 29.89/30.10  thf('126', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('127', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('128', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('129', plain,
% 29.89/30.10      (((m1_subset_1 @ sk_C @ 
% 29.89/30.10         (k1_zfmisc_1 @ 
% 29.89/30.10          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 29.89/30.10        | ~ (l1_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['127', '128'])).
% 29.89/30.10  thf('130', plain, ((l1_struct_0 @ sk_B)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('131', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 29.89/30.10      inference('demod', [status(thm)], ['129', '130'])).
% 29.89/30.10  thf('132', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.10  thf('133', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 29.89/30.10      inference('demod', [status(thm)], ['131', '132'])).
% 29.89/30.10  thf(cc5_funct_2, axiom,
% 29.89/30.10    (![A:$i,B:$i]:
% 29.89/30.10     ( ( ~( v1_xboole_0 @ B ) ) =>
% 29.89/30.10       ( ![C:$i]:
% 29.89/30.10         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.89/30.10           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 29.89/30.10             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 29.89/30.10  thf('134', plain,
% 29.89/30.10      (![X18 : $i, X19 : $i, X20 : $i]:
% 29.89/30.10         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 29.89/30.10          | (v1_partfun1 @ X18 @ X19)
% 29.89/30.10          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 29.89/30.10          | ~ (v1_funct_1 @ X18)
% 29.89/30.10          | (v1_xboole_0 @ X20))),
% 29.89/30.10      inference('cnf', [status(esa)], [cc5_funct_2])).
% 29.89/30.10  thf('135', plain,
% 29.89/30.10      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 29.89/30.10        | ~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 29.89/30.10        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 29.89/30.10      inference('sup-', [status(thm)], ['133', '134'])).
% 29.89/30.10  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('137', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('138', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('139', plain,
% 29.89/30.10      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 29.89/30.10        | ~ (l1_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['137', '138'])).
% 29.89/30.10  thf('140', plain, ((l1_struct_0 @ sk_B)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('141', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('demod', [status(thm)], ['139', '140'])).
% 29.89/30.10  thf('142', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.10  thf('143', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('demod', [status(thm)], ['141', '142'])).
% 29.89/30.10  thf('144', plain,
% 29.89/30.10      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 29.89/30.10        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 29.89/30.10      inference('demod', [status(thm)], ['135', '136', '143'])).
% 29.89/30.10  thf('145', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('clc', [status(thm)], ['8', '9'])).
% 29.89/30.10  thf('146', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 29.89/30.10      inference('clc', [status(thm)], ['144', '145'])).
% 29.89/30.10  thf('147', plain,
% 29.89/30.10      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 29.89/30.10      inference('sup+', [status(thm)], ['126', '146'])).
% 29.89/30.10  thf('148', plain, ((l1_struct_0 @ sk_A)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('149', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 29.89/30.10      inference('demod', [status(thm)], ['147', '148'])).
% 29.89/30.10  thf('150', plain,
% 29.89/30.10      (![X21 : $i, X22 : $i]:
% 29.89/30.10         (~ (v1_partfun1 @ X22 @ X21)
% 29.89/30.10          | ((k1_relat_1 @ X22) = (X21))
% 29.89/30.10          | ~ (v4_relat_1 @ X22 @ X21)
% 29.89/30.10          | ~ (v1_relat_1 @ X22))),
% 29.89/30.10      inference('cnf', [status(esa)], [d4_partfun1])).
% 29.89/30.10  thf('151', plain,
% 29.89/30.10      ((~ (v1_relat_1 @ sk_C)
% 29.89/30.10        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 29.89/30.10        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 29.89/30.10      inference('sup-', [status(thm)], ['149', '150'])).
% 29.89/30.10  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 29.89/30.10      inference('demod', [status(thm)], ['93', '94'])).
% 29.89/30.10  thf('153', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.10      inference('demod', [status(thm)], ['15', '16'])).
% 29.89/30.10  thf('154', plain,
% 29.89/30.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 29.89/30.10         ((v4_relat_1 @ X12 @ X13)
% 29.89/30.10          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 29.89/30.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 29.89/30.10  thf('155', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 29.89/30.10      inference('sup-', [status(thm)], ['153', '154'])).
% 29.89/30.10  thf('156', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 29.89/30.10      inference('demod', [status(thm)], ['151', '152', '155'])).
% 29.89/30.10  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 29.89/30.10      inference('demod', [status(thm)], ['93', '94'])).
% 29.89/30.10  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('160', plain,
% 29.89/30.10      ((((k6_partfun1 @ (k2_struct_0 @ sk_A))
% 29.89/30.10          != (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.10        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.89/30.10      inference('demod', [status(thm)], ['125', '156', '157', '158', '159'])).
% 29.89/30.10  thf('161', plain,
% 29.89/30.10      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.10      inference('simplify', [status(thm)], ['160'])).
% 29.89/30.10  thf('162', plain,
% 29.89/30.10      (![X9 : $i]:
% 29.89/30.10         (~ (v2_funct_1 @ X9)
% 29.89/30.10          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 29.89/30.10          | ~ (v1_funct_1 @ X9)
% 29.89/30.10          | ~ (v1_relat_1 @ X9))),
% 29.89/30.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 29.89/30.10  thf('163', plain,
% 29.89/30.10      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.10      inference('simplify', [status(thm)], ['109'])).
% 29.89/30.10  thf('164', plain,
% 29.89/30.10      (![X34 : $i]:
% 29.89/30.10         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.10  thf('165', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.10      inference('demod', [status(thm)], ['15', '16'])).
% 29.89/30.10  thf('166', plain,
% 29.89/30.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.89/30.10         (~ (v2_funct_1 @ X28)
% 29.89/30.10          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 29.89/30.10          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 29.89/30.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 29.89/30.10          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 29.89/30.10          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 29.89/30.10          | ~ (v1_funct_1 @ X28))),
% 29.89/30.10      inference('cnf', [status(esa)], [t31_funct_2])).
% 29.89/30.10  thf('167', plain,
% 29.89/30.10      ((~ (v1_funct_1 @ sk_C)
% 29.89/30.10        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 29.89/30.10        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10           (k1_zfmisc_1 @ 
% 29.89/30.10            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 29.89/30.10        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 29.89/30.10            != (u1_struct_0 @ sk_B))
% 29.89/30.10        | ~ (v2_funct_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['165', '166'])).
% 29.89/30.10  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('169', plain,
% 29.89/30.10      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 29.89/30.10      inference('demod', [status(thm)], ['41', '42'])).
% 29.89/30.10  thf('170', plain,
% 29.89/30.10      ((m1_subset_1 @ sk_C @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.10      inference('demod', [status(thm)], ['15', '16'])).
% 29.89/30.10  thf('171', plain,
% 29.89/30.10      (![X15 : $i, X16 : $i, X17 : $i]:
% 29.89/30.10         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 29.89/30.10          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 29.89/30.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 29.89/30.10  thf('172', plain,
% 29.89/30.10      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 29.89/30.10         = (k2_relat_1 @ sk_C))),
% 29.89/30.10      inference('sup-', [status(thm)], ['170', '171'])).
% 29.89/30.10  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('174', plain,
% 29.89/30.10      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10         (k1_zfmisc_1 @ 
% 29.89/30.10          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 29.89/30.10        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 29.89/30.10      inference('demod', [status(thm)], ['167', '168', '169', '172', '173'])).
% 29.89/30.10  thf('175', plain,
% 29.89/30.10      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 29.89/30.10        | ~ (l1_struct_0 @ sk_B)
% 29.89/30.10        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10           (k1_zfmisc_1 @ 
% 29.89/30.10            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 29.89/30.10      inference('sup-', [status(thm)], ['164', '174'])).
% 29.89/30.10  thf('176', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.10      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.10  thf('177', plain, ((l1_struct_0 @ sk_B)),
% 29.89/30.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.10  thf('178', plain,
% 29.89/30.10      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 29.89/30.10        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10           (k1_zfmisc_1 @ 
% 29.89/30.10            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 29.89/30.10      inference('demod', [status(thm)], ['175', '176', '177'])).
% 29.89/30.10  thf('179', plain,
% 29.89/30.10      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.10        (k1_zfmisc_1 @ 
% 29.89/30.10         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 29.89/30.10      inference('simplify', [status(thm)], ['178'])).
% 29.89/30.10  thf(d4_tops_2, axiom,
% 29.89/30.10    (![A:$i,B:$i,C:$i]:
% 29.89/30.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 29.89/30.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.89/30.10       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 29.89/30.10         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 29.89/30.10  thf('180', plain,
% 29.89/30.10      (![X36 : $i, X37 : $i, X38 : $i]:
% 29.89/30.10         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 29.89/30.10          | ~ (v2_funct_1 @ X38)
% 29.89/30.10          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 29.89/30.10          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 29.89/30.10          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 29.89/30.10          | ~ (v1_funct_1 @ X38))),
% 29.89/30.10      inference('cnf', [status(esa)], [d4_tops_2])).
% 29.89/30.10  thf('181', plain,
% 29.89/30.10      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.10        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11             (k2_struct_0 @ sk_A))
% 29.89/30.11        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.11        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.11        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 29.89/30.11      inference('sup-', [status(thm)], ['179', '180'])).
% 29.89/30.11  thf('182', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 29.89/30.11      inference('simplify', [status(thm)], ['77'])).
% 29.89/30.11  thf('183', plain,
% 29.89/30.11      (![X34 : $i]:
% 29.89/30.11         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.11  thf('184', plain,
% 29.89/30.11      ((m1_subset_1 @ sk_C @ 
% 29.89/30.11        (k1_zfmisc_1 @ 
% 29.89/30.11         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.11      inference('demod', [status(thm)], ['15', '16'])).
% 29.89/30.11  thf('185', plain,
% 29.89/30.11      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.89/30.11         (~ (v2_funct_1 @ X28)
% 29.89/30.11          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 29.89/30.11          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 29.89/30.11          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 29.89/30.11          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 29.89/30.11          | ~ (v1_funct_1 @ X28))),
% 29.89/30.11      inference('cnf', [status(esa)], [t31_funct_2])).
% 29.89/30.11  thf('186', plain,
% 29.89/30.11      ((~ (v1_funct_1 @ sk_C)
% 29.89/30.11        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 29.89/30.11        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11           (k2_struct_0 @ sk_A))
% 29.89/30.11        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 29.89/30.11            != (u1_struct_0 @ sk_B))
% 29.89/30.11        | ~ (v2_funct_1 @ sk_C))),
% 29.89/30.11      inference('sup-', [status(thm)], ['184', '185'])).
% 29.89/30.11  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('188', plain,
% 29.89/30.11      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 29.89/30.11      inference('demod', [status(thm)], ['41', '42'])).
% 29.89/30.11  thf('189', plain,
% 29.89/30.11      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 29.89/30.11         = (k2_relat_1 @ sk_C))),
% 29.89/30.11      inference('sup-', [status(thm)], ['170', '171'])).
% 29.89/30.11  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('191', plain,
% 29.89/30.11      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11         (k2_struct_0 @ sk_A))
% 29.89/30.11        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 29.89/30.11      inference('demod', [status(thm)], ['186', '187', '188', '189', '190'])).
% 29.89/30.11  thf('192', plain,
% 29.89/30.11      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 29.89/30.11        | ~ (l1_struct_0 @ sk_B)
% 29.89/30.11        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11           (k2_struct_0 @ sk_A)))),
% 29.89/30.11      inference('sup-', [status(thm)], ['183', '191'])).
% 29.89/30.11  thf('193', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.11      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.11  thf('194', plain, ((l1_struct_0 @ sk_B)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('195', plain,
% 29.89/30.11      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 29.89/30.11        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11           (k2_struct_0 @ sk_A)))),
% 29.89/30.11      inference('demod', [status(thm)], ['192', '193', '194'])).
% 29.89/30.11  thf('196', plain,
% 29.89/30.11      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11        (k2_struct_0 @ sk_A))),
% 29.89/30.11      inference('simplify', [status(thm)], ['195'])).
% 29.89/30.11  thf('197', plain,
% 29.89/30.11      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 29.89/30.11        (k1_zfmisc_1 @ 
% 29.89/30.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 29.89/30.11      inference('simplify', [status(thm)], ['178'])).
% 29.89/30.11  thf('198', plain,
% 29.89/30.11      (![X15 : $i, X16 : $i, X17 : $i]:
% 29.89/30.11         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 29.89/30.11          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 29.89/30.11      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 29.89/30.11  thf('199', plain,
% 29.89/30.11      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 29.89/30.11      inference('sup-', [status(thm)], ['197', '198'])).
% 29.89/30.11  thf('200', plain,
% 29.89/30.11      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.11        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 29.89/30.11        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 29.89/30.11      inference('demod', [status(thm)], ['181', '182', '196', '199'])).
% 29.89/30.11  thf('201', plain,
% 29.89/30.11      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.11        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 29.89/30.11        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.89/30.11      inference('sup-', [status(thm)], ['163', '200'])).
% 29.89/30.11  thf('202', plain,
% 29.89/30.11      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 29.89/30.11        | ~ (v1_relat_1 @ sk_C)
% 29.89/30.11        | ~ (v1_funct_1 @ sk_C)
% 29.89/30.11        | ~ (v2_funct_1 @ sk_C)
% 29.89/30.11        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.11        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.11      inference('sup-', [status(thm)], ['162', '201'])).
% 29.89/30.11  thf('203', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 29.89/30.11      inference('demod', [status(thm)], ['151', '152', '155'])).
% 29.89/30.11  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 29.89/30.11      inference('demod', [status(thm)], ['93', '94'])).
% 29.89/30.11  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('206', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('207', plain,
% 29.89/30.11      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 29.89/30.11        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 29.89/30.11        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.11      inference('demod', [status(thm)], ['202', '203', '204', '205', '206'])).
% 29.89/30.11  thf('208', plain,
% 29.89/30.11      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.11        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 29.89/30.11      inference('simplify', [status(thm)], ['207'])).
% 29.89/30.11  thf('209', plain,
% 29.89/30.11      (![X34 : $i]:
% 29.89/30.11         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.11  thf('210', plain,
% 29.89/30.11      (![X34 : $i]:
% 29.89/30.11         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 29.89/30.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 29.89/30.11  thf('211', plain,
% 29.89/30.11      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 29.89/30.11           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 29.89/30.11          sk_C)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('212', plain,
% 29.89/30.11      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 29.89/30.11           sk_C)
% 29.89/30.11        | ~ (l1_struct_0 @ sk_A))),
% 29.89/30.11      inference('sup-', [status(thm)], ['210', '211'])).
% 29.89/30.11  thf('213', plain, ((l1_struct_0 @ sk_A)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('214', plain,
% 29.89/30.11      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 29.89/30.11          sk_C)),
% 29.89/30.11      inference('demod', [status(thm)], ['212', '213'])).
% 29.89/30.11  thf('215', plain,
% 29.89/30.11      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 29.89/30.11           sk_C)
% 29.89/30.11        | ~ (l1_struct_0 @ sk_B))),
% 29.89/30.11      inference('sup-', [status(thm)], ['209', '214'])).
% 29.89/30.11  thf('216', plain, ((l1_struct_0 @ sk_B)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('217', plain,
% 29.89/30.11      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 29.89/30.11          sk_C)),
% 29.89/30.11      inference('demod', [status(thm)], ['215', '216'])).
% 29.89/30.11  thf('218', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 29.89/30.11      inference('clc', [status(thm)], ['144', '145'])).
% 29.89/30.11  thf('219', plain,
% 29.89/30.11      (![X21 : $i, X22 : $i]:
% 29.89/30.11         (~ (v1_partfun1 @ X22 @ X21)
% 29.89/30.11          | ((k1_relat_1 @ X22) = (X21))
% 29.89/30.11          | ~ (v4_relat_1 @ X22 @ X21)
% 29.89/30.11          | ~ (v1_relat_1 @ X22))),
% 29.89/30.11      inference('cnf', [status(esa)], [d4_partfun1])).
% 29.89/30.11  thf('220', plain,
% 29.89/30.11      ((~ (v1_relat_1 @ sk_C)
% 29.89/30.11        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 29.89/30.11        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 29.89/30.11      inference('sup-', [status(thm)], ['218', '219'])).
% 29.89/30.11  thf('221', plain, ((v1_relat_1 @ sk_C)),
% 29.89/30.11      inference('demod', [status(thm)], ['93', '94'])).
% 29.89/30.11  thf('222', plain,
% 29.89/30.11      ((m1_subset_1 @ sk_C @ 
% 29.89/30.11        (k1_zfmisc_1 @ 
% 29.89/30.11         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('223', plain,
% 29.89/30.11      (![X12 : $i, X13 : $i, X14 : $i]:
% 29.89/30.11         ((v4_relat_1 @ X12 @ X13)
% 29.89/30.11          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 29.89/30.11      inference('cnf', [status(esa)], [cc2_relset_1])).
% 29.89/30.11  thf('224', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 29.89/30.11      inference('sup-', [status(thm)], ['222', '223'])).
% 29.89/30.11  thf('225', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 29.89/30.11      inference('demod', [status(thm)], ['220', '221', '224'])).
% 29.89/30.11  thf('226', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 29.89/30.11      inference('demod', [status(thm)], ['151', '152', '155'])).
% 29.89/30.11  thf('227', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 29.89/30.11      inference('demod', [status(thm)], ['225', '226'])).
% 29.89/30.11  thf('228', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 29.89/30.11      inference('demod', [status(thm)], ['225', '226'])).
% 29.89/30.11  thf('229', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 29.89/30.11      inference('sup+', [status(thm)], ['2', '3'])).
% 29.89/30.11  thf('230', plain,
% 29.89/30.11      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 29.89/30.11          sk_C)),
% 29.89/30.11      inference('demod', [status(thm)], ['217', '227', '228', '229'])).
% 29.89/30.11  thf('231', plain,
% 29.89/30.11      ((m1_subset_1 @ sk_C @ 
% 29.89/30.11        (k1_zfmisc_1 @ 
% 29.89/30.11         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 29.89/30.11      inference('demod', [status(thm)], ['20', '21'])).
% 29.89/30.11  thf('232', plain,
% 29.89/30.11      (![X36 : $i, X37 : $i, X38 : $i]:
% 29.89/30.11         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 29.89/30.11          | ~ (v2_funct_1 @ X38)
% 29.89/30.11          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 29.89/30.11          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 29.89/30.11          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 29.89/30.11          | ~ (v1_funct_1 @ X38))),
% 29.89/30.11      inference('cnf', [status(esa)], [d4_tops_2])).
% 29.89/30.11  thf('233', plain,
% 29.89/30.11      ((~ (v1_funct_1 @ sk_C)
% 29.89/30.11        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 29.89/30.11        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.11            = (k2_funct_1 @ sk_C))
% 29.89/30.11        | ~ (v2_funct_1 @ sk_C)
% 29.89/30.11        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.11            != (k2_relat_1 @ sk_C)))),
% 29.89/30.11      inference('sup-', [status(thm)], ['231', '232'])).
% 29.89/30.11  thf('234', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('235', plain,
% 29.89/30.11      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 29.89/30.11      inference('demod', [status(thm)], ['46', '47'])).
% 29.89/30.11  thf('236', plain, ((v2_funct_1 @ sk_C)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('237', plain,
% 29.89/30.11      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.11         = (k2_relat_1 @ sk_C))),
% 29.89/30.11      inference('demod', [status(thm)], ['33', '34', '35'])).
% 29.89/30.11  thf('238', plain,
% 29.89/30.11      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.11          = (k2_funct_1 @ sk_C))
% 29.89/30.11        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 29.89/30.11      inference('demod', [status(thm)], ['233', '234', '235', '236', '237'])).
% 29.89/30.11  thf('239', plain,
% 29.89/30.11      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 29.89/30.11         = (k2_funct_1 @ sk_C))),
% 29.89/30.11      inference('simplify', [status(thm)], ['238'])).
% 29.89/30.11  thf('240', plain,
% 29.89/30.11      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 29.89/30.11           (k2_funct_1 @ sk_C)) @ 
% 29.89/30.11          sk_C)),
% 29.89/30.11      inference('demod', [status(thm)], ['230', '239'])).
% 29.89/30.11  thf('241', plain,
% 29.89/30.11      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 29.89/30.11           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 29.89/30.11        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.11      inference('sup-', [status(thm)], ['208', '240'])).
% 29.89/30.11  thf('242', plain,
% 29.89/30.11      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 29.89/30.11           sk_C)
% 29.89/30.11        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.11        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 29.89/30.11      inference('sup-', [status(thm)], ['161', '241'])).
% 29.89/30.11  thf('243', plain,
% 29.89/30.11      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 29.89/30.11        | ~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 29.89/30.11             sk_C))),
% 29.89/30.11      inference('simplify', [status(thm)], ['242'])).
% 29.89/30.11  thf('244', plain,
% 29.89/30.11      ((m1_subset_1 @ sk_C @ 
% 29.89/30.11        (k1_zfmisc_1 @ 
% 29.89/30.11         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.11      inference('demod', [status(thm)], ['15', '16'])).
% 29.89/30.11  thf('245', plain,
% 29.89/30.11      ((m1_subset_1 @ sk_C @ 
% 29.89/30.11        (k1_zfmisc_1 @ 
% 29.89/30.11         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 29.89/30.11      inference('demod', [status(thm)], ['15', '16'])).
% 29.89/30.11  thf(reflexivity_r2_funct_2, axiom,
% 29.89/30.11    (![A:$i,B:$i,C:$i,D:$i]:
% 29.89/30.11     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 29.89/30.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 29.89/30.11         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 29.89/30.11         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.89/30.11       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 29.89/30.11  thf('246', plain,
% 29.89/30.11      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 29.89/30.11         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 29.89/30.11          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 29.89/30.11          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 29.89/30.11          | ~ (v1_funct_1 @ X26)
% 29.89/30.11          | ~ (v1_funct_1 @ X27)
% 29.89/30.11          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 29.89/30.11          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 29.89/30.11      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 29.89/30.11  thf('247', plain,
% 29.89/30.11      (![X0 : $i]:
% 29.89/30.11         (~ (m1_subset_1 @ X0 @ 
% 29.89/30.11             (k1_zfmisc_1 @ 
% 29.89/30.11              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 29.89/30.11          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 29.89/30.11          | ~ (v1_funct_1 @ X0)
% 29.89/30.11          | ~ (v1_funct_1 @ sk_C)
% 29.89/30.11          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 29.89/30.11          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 29.89/30.11             sk_C))),
% 29.89/30.11      inference('sup-', [status(thm)], ['245', '246'])).
% 29.89/30.11  thf('248', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('249', plain,
% 29.89/30.11      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 29.89/30.11      inference('demod', [status(thm)], ['41', '42'])).
% 29.89/30.11  thf('250', plain,
% 29.89/30.11      (![X0 : $i]:
% 29.89/30.11         (~ (m1_subset_1 @ X0 @ 
% 29.89/30.11             (k1_zfmisc_1 @ 
% 29.89/30.11              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 29.89/30.11          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 29.89/30.11          | ~ (v1_funct_1 @ X0)
% 29.89/30.11          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 29.89/30.11             sk_C))),
% 29.89/30.11      inference('demod', [status(thm)], ['247', '248', '249'])).
% 29.89/30.11  thf('251', plain,
% 29.89/30.11      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 29.89/30.11        | ~ (v1_funct_1 @ sk_C)
% 29.89/30.11        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 29.89/30.11      inference('sup-', [status(thm)], ['244', '250'])).
% 29.89/30.11  thf('252', plain, ((v1_funct_1 @ sk_C)),
% 29.89/30.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.89/30.11  thf('253', plain,
% 29.89/30.11      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 29.89/30.11      inference('demod', [status(thm)], ['41', '42'])).
% 29.89/30.11  thf('254', plain,
% 29.89/30.11      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 29.89/30.11      inference('demod', [status(thm)], ['251', '252', '253'])).
% 29.89/30.11  thf('255', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 29.89/30.11      inference('demod', [status(thm)], ['243', '254'])).
% 29.89/30.11  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 29.89/30.11  thf('256', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 29.89/30.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 29.89/30.11  thf('257', plain, ($false),
% 29.89/30.11      inference('demod', [status(thm)], ['10', '255', '256'])).
% 29.89/30.11  
% 29.89/30.11  % SZS output end Refutation
% 29.89/30.11  
% 29.94/30.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
