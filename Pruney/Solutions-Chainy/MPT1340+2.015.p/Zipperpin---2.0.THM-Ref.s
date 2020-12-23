%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mPedLiy6M0

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:07 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  376 (24730 expanded)
%              Number of leaves         :   38 (7074 expanded)
%              Depth                    :   39
%              Number of atoms          : 3810 (551324 expanded)
%              Number of equality atoms :  188 (15580 expanded)
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
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

thf('2',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('14',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('35',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','40'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('53',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','50','51','52'])).

thf('54',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','40'])).

thf('67',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('74',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('75',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['64','76'])).

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

thf('78',plain,(
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

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['81','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['95','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('108',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','93','94','108'])).

thf('110',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['53','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['64','76'])).

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

thf('113',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
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

thf('122',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['64','76'])).

thf('124',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('128',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['64','76'])).

thf('133',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X20 ) @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','131','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('143',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('144',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['141','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['64','76'])).

thf('147',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('149',plain,(
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

thf('150',plain,(
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

thf('151',plain,(
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
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
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
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
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
    inference('sup-',[status(thm)],['148','152'])).

thf('154',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','156'])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('159',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('160',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49'])).

thf('161',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','161'])).

thf('163',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['146','162'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('166',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('167',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('170',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('171',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
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

thf('173',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('176',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('178',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('179',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('181',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176','181'])).

thf('183',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','182'])).

thf('184',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('185',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('190',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','164','167','187','188','189'])).

thf('191',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['145','191'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('193',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('194',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('196',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('197',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('200',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('201',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['197','198','199','200','201'])).

thf('203',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['194','202'])).

thf('204',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('205',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('209',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('211',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('212',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('213',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X20 ) @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('214',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('217',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['214','215','216','217','218'])).

thf('220',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','219'])).

thf('221',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('222',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','210','224'])).

thf('226',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('227',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('228',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['225','228'])).

thf('230',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('231',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('234',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('235',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('236',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('238',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('240',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != X14 )
      | ( v1_partfun1 @ X15 @ X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('241',plain,(
    ! [X15: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v4_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
      | ( v1_partfun1 @ X15 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['239','241'])).

thf('243',plain,(
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
    inference('sup-',[status(thm)],['238','242'])).

thf('244',plain,(
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
    inference('sup-',[status(thm)],['237','243'])).

thf('245',plain,(
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
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
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
    inference('sup-',[status(thm)],['236','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['235','247'])).

thf('249',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('250',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('253',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('254',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('256',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('257',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('259',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['248','249','250','251','254','257','258'])).

thf('260',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['234','259'])).

thf('261',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['260','261','262','263'])).

thf('265',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['233','264'])).

thf('266',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('267',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('268',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('269',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['265','266','267','268'])).

thf('270',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('271',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('273',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['232','273'])).

thf('275',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('276',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('277',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['274','275','276','277','278'])).

thf('280',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['231','279'])).

thf('281',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['280'])).

thf('282',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['169','170'])).

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

thf('283',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_funct_2 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['284','285','286'])).

thf('288',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['281','287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('290',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('291',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('292',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('294',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['223'])).

thf('295',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['292','293','294'])).

thf('296',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('297',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['295','296'])).

thf('298',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('299',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['289','299'])).

thf('301',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('302',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['300','301','302','303'])).

thf('305',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['304'])).

thf('306',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('307',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X20 ) @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('308',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['306','307'])).

thf('309',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('310',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['223'])).

thf('311',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['308','309','310'])).

thf('312',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('313',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['311','312'])).

thf('314',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('315',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['313','314'])).

thf('316',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['274','275','276','277','278'])).

thf('317',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('318',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['288','305','318'])).

thf('320',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['193','319'])).

thf('321',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('322',plain,(
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

thf('323',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_funct_2 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['322'])).

thf('324',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['321','323'])).

thf('325',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('326',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['324','325','326'])).

thf('328',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('329',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['320','327','328','329','330'])).

thf('332',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['274','275','276','277','278'])).

thf('333',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['192','331','332'])).

thf('334',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['333'])).

thf('335',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['324','325','326'])).

thf('336',plain,(
    $false ),
    inference(demod,[status(thm)],['111','334','335'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mPedLiy6M0
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 428 iterations in 0.239s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.70  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.70  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(d3_struct_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf(t64_tops_2, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_struct_0 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.70                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.70                 ( m1_subset_1 @
% 0.46/0.70                   C @ 
% 0.46/0.70                   ( k1_zfmisc_1 @
% 0.46/0.70                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.70               ( ( ( ( k2_relset_1 @
% 0.46/0.70                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.70                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.70                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.70                 ( r2_funct_2 @
% 0.46/0.70                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.70                   ( k2_tops_2 @
% 0.46/0.70                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.70                     ( k2_tops_2 @
% 0.46/0.70                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.70                   C ) ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( l1_struct_0 @ A ) =>
% 0.46/0.70          ( ![B:$i]:
% 0.46/0.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.70              ( ![C:$i]:
% 0.46/0.70                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.70                    ( v1_funct_2 @
% 0.46/0.70                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.70                    ( m1_subset_1 @
% 0.46/0.70                      C @ 
% 0.46/0.70                      ( k1_zfmisc_1 @
% 0.46/0.70                        ( k2_zfmisc_1 @
% 0.46/0.70                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.70                  ( ( ( ( k2_relset_1 @
% 0.46/0.70                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.70                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.70                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.70                    ( r2_funct_2 @
% 0.46/0.70                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.70                      ( k2_tops_2 @
% 0.46/0.70                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.70                        ( k2_tops_2 @
% 0.46/0.70                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.70                      C ) ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70           sk_C)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.70  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.46/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('10', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['5', '10'])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70           sk_C)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['0', '11'])).
% 0.46/0.70  thf('13', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf(cc5_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.70       ( ![C:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.70             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.46/0.70          | (v1_partfun1 @ X11 @ X12)
% 0.46/0.70          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.46/0.70          | ~ (v1_funct_1 @ X11)
% 0.46/0.70          | (v1_xboole_0 @ X13))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.70  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.70  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['24', '25', '32'])).
% 0.46/0.70  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf(fc5_struct_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.70       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (~ (v1_xboole_0 @ (k2_struct_0 @ X24))
% 0.46/0.70          | ~ (l1_struct_0 @ X24)
% 0.46/0.70          | (v2_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v2_struct_0 @ sk_B)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.70  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.70  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('40', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('clc', [status(thm)], ['38', '39'])).
% 0.46/0.70  thf('41', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('clc', [status(thm)], ['33', '40'])).
% 0.46/0.70  thf(d4_partfun1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.70       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         (~ (v1_partfun1 @ X15 @ X14)
% 0.46/0.70          | ((k1_relat_1 @ X15) = (X14))
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ X14)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( v1_relat_1 @ C ) ))).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X2)
% 0.46/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X5 @ X6)
% 0.46/0.70          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('49', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.70  thf('50', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '46', '49'])).
% 0.46/0.70  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '46', '49'])).
% 0.46/0.70  thf('52', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '46', '49'])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['15', '50', '51', '52'])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('60', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['54', '59'])).
% 0.46/0.70  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.70  thf('63', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.70  thf('65', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('66', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('clc', [status(thm)], ['33', '40'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['65', '66'])).
% 0.46/0.70  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('69', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         (~ (v1_partfun1 @ X15 @ X14)
% 0.46/0.70          | ((k1_relat_1 @ X15) = (X14))
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ X14)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.70  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('73', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('74', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X5 @ X6)
% 0.46/0.70          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('75', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.70  thf('76', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.46/0.70  thf('77', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['64', '76'])).
% 0.46/0.70  thf(d4_tops_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.70         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.70  thf('78', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.46/0.70          | ~ (v2_funct_1 @ X27)
% 0.46/0.70          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.46/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.46/0.70          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.46/0.70          | ~ (v1_funct_1 @ X27))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.70  thf('79', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.70  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('81', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('82', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('83', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('84', plain,
% 0.46/0.70      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['82', '83'])).
% 0.46/0.70  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('86', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.70  thf('87', plain,
% 0.46/0.70      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['81', '86'])).
% 0.46/0.70  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('89', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.46/0.70  thf('90', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('91', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['89', '90'])).
% 0.46/0.70  thf('92', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.46/0.70  thf('93', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.70  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('95', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('96', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('97', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('98', plain,
% 0.46/0.70      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70          = (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['96', '97'])).
% 0.46/0.70  thf('99', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('100', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['98', '99'])).
% 0.46/0.70  thf('101', plain,
% 0.46/0.70      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70          = (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['95', '100'])).
% 0.46/0.70  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('103', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['101', '102'])).
% 0.46/0.70  thf('104', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('105', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('106', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.46/0.70  thf('107', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.46/0.70  thf('108', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.70  thf('109', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70          = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['79', '80', '93', '94', '108'])).
% 0.46/0.70  thf('110', plain,
% 0.46/0.70      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['109'])).
% 0.46/0.70  thf('111', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['53', '110'])).
% 0.46/0.70  thf('112', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['64', '76'])).
% 0.46/0.70  thf(t31_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.70           ( m1_subset_1 @
% 0.46/0.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('113', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (m1_subset_1 @ (k2_funct_1 @ X20) @ 
% 0.46/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('114', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['112', '113'])).
% 0.46/0.70  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('116', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.70  thf('117', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.70  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('119', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 0.46/0.70  thf('120', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['119'])).
% 0.46/0.70  thf('121', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.46/0.70          | ~ (v2_funct_1 @ X27)
% 0.46/0.70          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.46/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.46/0.70          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.46/0.70          | ~ (v1_funct_1 @ X27))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.70  thf('122', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70             (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['120', '121'])).
% 0.46/0.70  thf('123', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['64', '76'])).
% 0.46/0.70  thf('124', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (v1_funct_1 @ (k2_funct_1 @ X20))
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('125', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['123', '124'])).
% 0.46/0.70  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('127', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.70  thf('128', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.70  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('130', plain,
% 0.46/0.70      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 0.46/0.70  thf('131', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['130'])).
% 0.46/0.70  thf('132', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['64', '76'])).
% 0.46/0.70  thf('133', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (v1_funct_2 @ (k2_funct_1 @ X20) @ X21 @ X22)
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('134', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70           (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['132', '133'])).
% 0.46/0.70  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('136', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.70  thf('137', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.70  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('139', plain,
% 0.46/0.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70         (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 0.46/0.70  thf('140', plain,
% 0.46/0.70      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70        (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['139'])).
% 0.46/0.70  thf('141', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['122', '131', '140'])).
% 0.46/0.70  thf('142', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['119'])).
% 0.46/0.70  thf('143', plain,
% 0.46/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.46/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('144', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['142', '143'])).
% 0.46/0.70  thf('145', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['141', '144'])).
% 0.46/0.70  thf('146', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['64', '76'])).
% 0.46/0.70  thf('147', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '46', '49'])).
% 0.46/0.70  thf('148', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('149', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf(t63_tops_2, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_struct_0 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( l1_struct_0 @ B ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.70                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.70                 ( m1_subset_1 @
% 0.46/0.70                   C @ 
% 0.46/0.70                   ( k1_zfmisc_1 @
% 0.46/0.70                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.70               ( ( ( ( k2_relset_1 @
% 0.46/0.70                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.70                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.70                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.70                 ( v2_funct_1 @
% 0.46/0.70                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf('150', plain,
% 0.46/0.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.70         (~ (l1_struct_0 @ X28)
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28) @ X30)
% 0.46/0.70              != (k2_struct_0 @ X28))
% 0.46/0.70          | ~ (v2_funct_1 @ X30)
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28) @ X30))
% 0.46/0.70          | ~ (m1_subset_1 @ X30 @ 
% 0.46/0.70               (k1_zfmisc_1 @ 
% 0.46/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.46/0.70          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.46/0.70          | ~ (v1_funct_1 @ X30)
% 0.46/0.70          | ~ (l1_struct_0 @ X29))),
% 0.46/0.70      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.46/0.70  thf('151', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X2 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.46/0.70          | ~ (l1_struct_0 @ X0)
% 0.46/0.70          | ~ (l1_struct_0 @ X1)
% 0.46/0.70          | ~ (v1_funct_1 @ X2)
% 0.46/0.70          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.46/0.70          | ~ (v2_funct_1 @ X2)
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.46/0.70              != (k2_struct_0 @ X0))
% 0.46/0.70          | ~ (l1_struct_0 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['149', '150'])).
% 0.46/0.70  thf('152', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.46/0.70            != (k2_struct_0 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ X2)
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.46/0.70          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ X2)
% 0.46/0.70          | ~ (l1_struct_0 @ X1)
% 0.46/0.70          | ~ (l1_struct_0 @ X0)
% 0.46/0.70          | ~ (m1_subset_1 @ X2 @ 
% 0.46/0.70               (k1_zfmisc_1 @ 
% 0.46/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['151'])).
% 0.46/0.70  thf('153', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.46/0.70          | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70          | ~ (l1_struct_0 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.46/0.70          | ~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.46/0.70              != (k2_struct_0 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['148', '152'])).
% 0.46/0.70  thf('154', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('155', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('156', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.46/0.70          | ~ (l1_struct_0 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.46/0.70          | ~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.46/0.70              != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.46/0.70  thf('157', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0)
% 0.46/0.70              != (k2_relat_1 @ sk_C))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0))
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['147', '156'])).
% 0.46/0.70  thf('158', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '46', '49'])).
% 0.46/0.70  thf('159', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '46', '49'])).
% 0.46/0.70  thf('160', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '46', '49'])).
% 0.46/0.70  thf('161', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('162', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.46/0.70          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0)
% 0.46/0.70              != (k2_relat_1 @ sk_C))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0))
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | ~ (v1_funct_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 0.46/0.70  thf('163', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | (v2_funct_1 @ 
% 0.46/0.70           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['146', '162'])).
% 0.46/0.70  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('165', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.70  thf('166', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.46/0.70  thf('167', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['165', '166'])).
% 0.46/0.70  thf('168', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('169', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('170', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.46/0.70  thf('171', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['169', '170'])).
% 0.46/0.70  thf('172', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.46/0.70          | ~ (v2_funct_1 @ X27)
% 0.46/0.70          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.46/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.46/0.70          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.46/0.70          | ~ (v1_funct_1 @ X27))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.70  thf('173', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['171', '172'])).
% 0.46/0.70  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('175', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['165', '166'])).
% 0.46/0.70  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('177', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('178', plain,
% 0.46/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.46/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('179', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['177', '178'])).
% 0.46/0.70  thf('180', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.46/0.70  thf('181', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['179', '180'])).
% 0.46/0.70  thf('182', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70          = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['173', '174', '175', '176', '181'])).
% 0.46/0.70  thf('183', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['168', '182'])).
% 0.46/0.70  thf('184', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('185', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('186', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.46/0.70  thf('187', plain,
% 0.46/0.70      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['186'])).
% 0.46/0.70  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('189', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['179', '180'])).
% 0.46/0.70  thf('190', plain,
% 0.46/0.70      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)],
% 0.46/0.70                ['163', '164', '167', '187', '188', '189'])).
% 0.46/0.70  thf('191', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['190'])).
% 0.46/0.70  thf('192', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['145', '191'])).
% 0.46/0.70  thf(t65_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.70       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.70  thf('193', plain,
% 0.46/0.70      (![X1 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('194', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('195', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['169', '170'])).
% 0.46/0.70  thf('196', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (m1_subset_1 @ (k2_funct_1 @ X20) @ 
% 0.46/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('197', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (u1_struct_0 @ sk_B))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['195', '196'])).
% 0.46/0.70  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('199', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['165', '166'])).
% 0.46/0.70  thf('200', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['179', '180'])).
% 0.46/0.70  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('202', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['197', '198', '199', '200', '201'])).
% 0.46/0.70  thf('203', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['194', '202'])).
% 0.46/0.70  thf('204', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('205', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('206', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.46/0.70      inference('demod', [status(thm)], ['203', '204', '205'])).
% 0.46/0.70  thf('207', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['206'])).
% 0.46/0.70  thf('208', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (m1_subset_1 @ (k2_funct_1 @ X20) @ 
% 0.46/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('209', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70             (k1_relat_1 @ sk_C))
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['207', '208'])).
% 0.46/0.70  thf('210', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['130'])).
% 0.46/0.70  thf('211', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('212', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['169', '170'])).
% 0.46/0.70  thf('213', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (v1_funct_2 @ (k2_funct_1 @ X20) @ X21 @ X22)
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('214', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (u1_struct_0 @ sk_B))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['212', '213'])).
% 0.46/0.70  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('216', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['165', '166'])).
% 0.46/0.70  thf('217', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['179', '180'])).
% 0.46/0.70  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('219', plain,
% 0.46/0.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70         (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['214', '215', '216', '217', '218'])).
% 0.46/0.70  thf('220', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['211', '219'])).
% 0.46/0.70  thf('221', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('222', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('223', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['220', '221', '222'])).
% 0.46/0.70  thf('224', plain,
% 0.46/0.70      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70        (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['223'])).
% 0.46/0.70  thf('225', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['209', '210', '224'])).
% 0.46/0.70  thf('226', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['206'])).
% 0.46/0.70  thf('227', plain,
% 0.46/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.46/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('228', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['226', '227'])).
% 0.46/0.70  thf('229', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['225', '228'])).
% 0.46/0.70  thf('230', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['190'])).
% 0.46/0.70  thf('231', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['229', '230'])).
% 0.46/0.70  thf(t55_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.70       ( ( v2_funct_1 @ A ) =>
% 0.46/0.70         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.70           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('232', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X0)
% 0.46/0.70          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('233', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X0)
% 0.46/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('234', plain,
% 0.46/0.70      (![X1 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('235', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['190'])).
% 0.46/0.70  thf('236', plain,
% 0.46/0.70      (![X1 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('237', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X0)
% 0.46/0.70          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('238', plain,
% 0.46/0.70      (![X1 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('239', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X0)
% 0.46/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('240', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         (((k1_relat_1 @ X15) != (X14))
% 0.46/0.70          | (v1_partfun1 @ X15 @ X14)
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ X14)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('241', plain,
% 0.46/0.70      (![X15 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X15)
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ (k1_relat_1 @ X15))
% 0.46/0.70          | (v1_partfun1 @ X15 @ (k1_relat_1 @ X15)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['240'])).
% 0.46/0.70  thf('242', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['239', '241'])).
% 0.46/0.70  thf('243', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['238', '242'])).
% 0.46/0.70  thf('244', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['237', '243'])).
% 0.46/0.70  thf('245', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['244'])).
% 0.46/0.70  thf('246', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['236', '245'])).
% 0.46/0.70  thf('247', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['246'])).
% 0.46/0.70  thf('248', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['235', '247'])).
% 0.46/0.70  thf('249', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('250', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('251', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('252', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.70  thf('253', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.46/0.70  thf('254', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['252', '253'])).
% 0.46/0.70  thf('255', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['119'])).
% 0.46/0.70  thf('256', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X2)
% 0.46/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('257', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['255', '256'])).
% 0.46/0.70  thf('258', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['130'])).
% 0.46/0.70  thf('259', plain,
% 0.46/0.70      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)],
% 0.46/0.70                ['248', '249', '250', '251', '254', '257', '258'])).
% 0.46/0.70  thf('260', plain,
% 0.46/0.70      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['234', '259'])).
% 0.46/0.70  thf('261', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('263', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('264', plain,
% 0.46/0.70      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['260', '261', '262', '263'])).
% 0.46/0.70  thf('265', plain,
% 0.46/0.70      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['233', '264'])).
% 0.46/0.70  thf('266', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['255', '256'])).
% 0.46/0.70  thf('267', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['130'])).
% 0.46/0.70  thf('268', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['190'])).
% 0.46/0.70  thf('269', plain,
% 0.46/0.70      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['265', '266', '267', '268'])).
% 0.46/0.70  thf('270', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         (~ (v1_partfun1 @ X15 @ X14)
% 0.46/0.70          | ((k1_relat_1 @ X15) = (X14))
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ X14)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('271', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['269', '270'])).
% 0.46/0.70  thf('272', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('273', plain,
% 0.46/0.70      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['271', '272'])).
% 0.46/0.70  thf('274', plain,
% 0.46/0.70      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['232', '273'])).
% 0.46/0.70  thf('275', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['252', '253'])).
% 0.46/0.70  thf('276', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('277', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('278', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('279', plain,
% 0.46/0.70      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['274', '275', '276', '277', '278'])).
% 0.46/0.70  thf('280', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['231', '279'])).
% 0.46/0.70  thf('281', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['280'])).
% 0.46/0.70  thf('282', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['169', '170'])).
% 0.46/0.70  thf(redefinition_r2_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.70         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.70  thf('283', plain,
% 0.46/0.70      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.46/0.70          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.46/0.70          | ~ (v1_funct_1 @ X16)
% 0.46/0.70          | ~ (v1_funct_1 @ X19)
% 0.46/0.70          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.46/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.46/0.70          | ((X16) = (X19))
% 0.46/0.70          | ~ (r2_funct_2 @ X17 @ X18 @ X16 @ X19))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.46/0.70  thf('284', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.70             X0)
% 0.46/0.70          | ((sk_C) = (X0))
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ 
% 0.46/0.70               (k1_zfmisc_1 @ 
% 0.46/0.70                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['282', '283'])).
% 0.46/0.70  thf('285', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('286', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['165', '166'])).
% 0.46/0.70  thf('287', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.70             X0)
% 0.46/0.70          | ((sk_C) = (X0))
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ 
% 0.46/0.70               (k1_zfmisc_1 @ 
% 0.46/0.70                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | ~ (v1_funct_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['284', '285', '286'])).
% 0.46/0.70  thf('288', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70             (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.70             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['281', '287'])).
% 0.46/0.70  thf('289', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X0)
% 0.46/0.70          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('290', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['206'])).
% 0.46/0.70  thf('291', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (v1_funct_1 @ (k2_funct_1 @ X20))
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('292', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70             (k1_relat_1 @ sk_C))
% 0.46/0.70        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['290', '291'])).
% 0.46/0.70  thf('293', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['130'])).
% 0.46/0.70  thf('294', plain,
% 0.46/0.70      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70        (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['223'])).
% 0.46/0.70  thf('295', plain,
% 0.46/0.70      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['292', '293', '294'])).
% 0.46/0.70  thf('296', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['226', '227'])).
% 0.46/0.70  thf('297', plain,
% 0.46/0.70      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['295', '296'])).
% 0.46/0.70  thf('298', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['190'])).
% 0.46/0.71  thf('299', plain,
% 0.46/0.71      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.71        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['297', '298'])).
% 0.46/0.71  thf('300', plain,
% 0.46/0.71      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.46/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.71        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['289', '299'])).
% 0.46/0.71  thf('301', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.71  thf('302', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('303', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('304', plain,
% 0.46/0.71      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.46/0.71        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)], ['300', '301', '302', '303'])).
% 0.46/0.71  thf('305', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['304'])).
% 0.46/0.71  thf('306', plain,
% 0.46/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.71      inference('simplify', [status(thm)], ['206'])).
% 0.46/0.71  thf('307', plain,
% 0.46/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.71         (~ (v2_funct_1 @ X20)
% 0.46/0.71          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.71          | (v1_funct_2 @ (k2_funct_1 @ X20) @ X21 @ X22)
% 0.46/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.71          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.71          | ~ (v1_funct_1 @ X20))),
% 0.46/0.71      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.71  thf('308', plain,
% 0.46/0.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.71        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.71             (k1_relat_1 @ sk_C))
% 0.46/0.71        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.71           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['306', '307'])).
% 0.46/0.71  thf('309', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['130'])).
% 0.46/0.71  thf('310', plain,
% 0.46/0.71      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.71        (k1_relat_1 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['223'])).
% 0.46/0.71  thf('311', plain,
% 0.46/0.71      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.71         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['308', '309', '310'])).
% 0.46/0.71  thf('312', plain,
% 0.46/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['226', '227'])).
% 0.46/0.71  thf('313', plain,
% 0.46/0.71      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.71         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['311', '312'])).
% 0.46/0.71  thf('314', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['190'])).
% 0.46/0.71  thf('315', plain,
% 0.46/0.71      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.71         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['313', '314'])).
% 0.46/0.71  thf('316', plain,
% 0.46/0.71      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['274', '275', '276', '277', '278'])).
% 0.46/0.71  thf('317', plain,
% 0.46/0.71      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.71         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['315', '316'])).
% 0.46/0.71  thf('318', plain,
% 0.46/0.71      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.71        (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('simplify', [status(thm)], ['317'])).
% 0.46/0.71  thf('319', plain,
% 0.46/0.71      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.71        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.71             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)], ['288', '305', '318'])).
% 0.46/0.71  thf('320', plain,
% 0.46/0.71      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.71           sk_C)
% 0.46/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.71        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['193', '319'])).
% 0.46/0.71  thf('321', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['169', '170'])).
% 0.46/0.71  thf('322', plain,
% 0.46/0.71      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.46/0.71          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.46/0.71          | ~ (v1_funct_1 @ X16)
% 0.46/0.71          | ~ (v1_funct_1 @ X19)
% 0.46/0.71          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.46/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.46/0.71          | (r2_funct_2 @ X17 @ X18 @ X16 @ X19)
% 0.46/0.71          | ((X16) != (X19)))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.46/0.71  thf('323', plain,
% 0.46/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.71         ((r2_funct_2 @ X17 @ X18 @ X19 @ X19)
% 0.46/0.71          | ~ (v1_funct_1 @ X19)
% 0.46/0.71          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.46/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.71      inference('simplify', [status(thm)], ['322'])).
% 0.46/0.71  thf('324', plain,
% 0.46/0.71      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.71           sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['321', '323'])).
% 0.46/0.71  thf('325', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['165', '166'])).
% 0.46/0.71  thf('326', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('327', plain,
% 0.46/0.71      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['324', '325', '326'])).
% 0.46/0.71  thf('328', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.71  thf('329', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('330', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('331', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['320', '327', '328', '329', '330'])).
% 0.46/0.71  thf('332', plain,
% 0.46/0.71      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['274', '275', '276', '277', '278'])).
% 0.46/0.71  thf('333', plain,
% 0.46/0.71      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.46/0.71        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['192', '331', '332'])).
% 0.46/0.71  thf('334', plain,
% 0.46/0.71      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['333'])).
% 0.46/0.71  thf('335', plain,
% 0.46/0.71      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['324', '325', '326'])).
% 0.46/0.71  thf('336', plain, ($false),
% 0.46/0.71      inference('demod', [status(thm)], ['111', '334', '335'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
