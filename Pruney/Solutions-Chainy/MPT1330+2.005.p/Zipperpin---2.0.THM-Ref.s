%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Cy1qgHP1Q0

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:42 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  202 (2208 expanded)
%              Number of leaves         :   39 ( 642 expanded)
%              Depth                    :   27
%              Number of atoms          : 1600 (29815 expanded)
%              Number of equality atoms :  180 (2810 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t52_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_struct_0 @ B )
                      = k1_xboole_0 )
                   => ( ( k2_struct_0 @ A )
                      = k1_xboole_0 ) )
                 => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','18'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('47',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('49',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('63',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k8_relset_1 @ X20 @ X21 @ X22 @ X21 )
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('64',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('67',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('68',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('71',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','18'])).

thf('74',plain,
    ( ( ( v1_partfun1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('76',plain,
    ( ( ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('78',plain,
    ( ( ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('80',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('81',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('82',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('83',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('85',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('89',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('90',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','87','92'])).

thf('94',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('96',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('98',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('101',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('102',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X28 @ X29 )
        = X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','87','92'])).

thf('111',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('113',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('114',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','114'])).

thf('116',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('117',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('118',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( ( ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','118'])).

thf('120',plain,
    ( ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['109','119'])).

thf('121',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','121'])).

thf('123',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','122'])).

thf('124',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('125',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('132',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['123','132'])).

thf('134',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('135',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['37','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','136'])).

thf('138',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k8_relset_1 @ X20 @ X21 @ X22 @ X21 )
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('139',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('141',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('142',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['37','135'])).

thf('144',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','144'])).

thf('146',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('147',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('148',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('149',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['146','155'])).

thf('157',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('158',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['133','134'])).

thf('160',plain,(
    ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['158','159'])).

thf('161',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['145','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Cy1qgHP1Q0
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.88  % Solved by: fo/fo7.sh
% 0.67/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.88  % done 971 iterations in 0.425s
% 0.67/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.88  % SZS output start Refutation
% 0.67/0.88  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.67/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.88  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.67/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.67/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.67/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.88  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.67/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.88  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.67/0.88  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.67/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.88  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.67/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.88  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.67/0.88  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.67/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.88  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.67/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.88  thf(d3_struct_0, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.67/0.88  thf('0', plain,
% 0.67/0.88      (![X30 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf('1', plain,
% 0.67/0.88      (![X30 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf(t52_tops_2, conjecture,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_struct_0 @ A ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( l1_struct_0 @ B ) =>
% 0.67/0.88           ( ![C:$i]:
% 0.67/0.88             ( ( ( v1_funct_1 @ C ) & 
% 0.67/0.88                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.67/0.88                 ( m1_subset_1 @
% 0.67/0.88                   C @ 
% 0.67/0.88                   ( k1_zfmisc_1 @
% 0.67/0.88                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.67/0.88               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.67/0.88                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.88                 ( ( k8_relset_1 @
% 0.67/0.88                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.67/0.88                     ( k2_struct_0 @ B ) ) =
% 0.67/0.88                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.88    (~( ![A:$i]:
% 0.67/0.88        ( ( l1_struct_0 @ A ) =>
% 0.67/0.88          ( ![B:$i]:
% 0.67/0.88            ( ( l1_struct_0 @ B ) =>
% 0.67/0.88              ( ![C:$i]:
% 0.67/0.88                ( ( ( v1_funct_1 @ C ) & 
% 0.67/0.88                    ( v1_funct_2 @
% 0.67/0.88                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.67/0.88                    ( m1_subset_1 @
% 0.67/0.88                      C @ 
% 0.67/0.88                      ( k1_zfmisc_1 @
% 0.67/0.88                        ( k2_zfmisc_1 @
% 0.67/0.88                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.67/0.88                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.67/0.88                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.88                    ( ( k8_relset_1 @
% 0.67/0.88                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.67/0.88                        ( k2_struct_0 @ B ) ) =
% 0.67/0.88                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.67/0.88    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.67/0.88  thf('2', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('3', plain,
% 0.67/0.88      (((m1_subset_1 @ sk_C @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.67/0.88        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup+', [status(thm)], ['1', '2'])).
% 0.67/0.88  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('5', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.88  thf('6', plain,
% 0.67/0.88      (((m1_subset_1 @ sk_C @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.67/0.88        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.88      inference('sup+', [status(thm)], ['0', '5'])).
% 0.67/0.88  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('8', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.88  thf('9', plain,
% 0.67/0.88      (![X30 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf('10', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.88  thf(cc5_funct_2, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.67/0.88       ( ![C:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.88           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.67/0.88             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.67/0.88  thf('11', plain,
% 0.67/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.67/0.88          | (v1_partfun1 @ X23 @ X24)
% 0.67/0.88          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.67/0.88          | ~ (v1_funct_1 @ X23)
% 0.67/0.88          | (v1_xboole_0 @ X25))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.67/0.88  thf('12', plain,
% 0.67/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.67/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.88        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.88        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.67/0.88  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('14', plain,
% 0.67/0.88      (![X30 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf('15', plain,
% 0.67/0.88      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('16', plain,
% 0.67/0.88      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.67/0.88        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup+', [status(thm)], ['14', '15'])).
% 0.67/0.88  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('18', plain,
% 0.67/0.88      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.88      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.88  thf('19', plain,
% 0.67/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.67/0.88        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['12', '13', '18'])).
% 0.67/0.88  thf(d4_partfun1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.67/0.88       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.67/0.88  thf('20', plain,
% 0.67/0.88      (![X26 : $i, X27 : $i]:
% 0.67/0.88         (~ (v1_partfun1 @ X27 @ X26)
% 0.67/0.88          | ((k1_relat_1 @ X27) = (X26))
% 0.67/0.88          | ~ (v4_relat_1 @ X27 @ X26)
% 0.67/0.88          | ~ (v1_relat_1 @ X27))),
% 0.67/0.88      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.67/0.88  thf('21', plain,
% 0.67/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.67/0.88        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.88        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.67/0.88        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['19', '20'])).
% 0.67/0.88  thf('22', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(cc1_relset_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.88       ( v1_relat_1 @ C ) ))).
% 0.67/0.88  thf('23', plain,
% 0.67/0.88      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.67/0.88         ((v1_relat_1 @ X8)
% 0.67/0.88          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.88  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.88      inference('sup-', [status(thm)], ['22', '23'])).
% 0.67/0.88  thf('25', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.88  thf(cc2_relset_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.88       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.67/0.88  thf('26', plain,
% 0.67/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.67/0.88         ((v4_relat_1 @ X11 @ X12)
% 0.67/0.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.67/0.88  thf('27', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.88  thf('28', plain,
% 0.67/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.67/0.88        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.67/0.88  thf(l13_xboole_0, axiom,
% 0.67/0.88    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.88  thf('29', plain,
% 0.67/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.88  thf('30', plain,
% 0.67/0.88      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.67/0.88        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.88  thf('31', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.88        | ~ (l1_struct_0 @ sk_B)
% 0.67/0.88        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup+', [status(thm)], ['9', '30'])).
% 0.67/0.88  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('33', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.88        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['31', '32'])).
% 0.67/0.88  thf('34', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.67/0.88        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('35', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.67/0.88         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.67/0.88      inference('split', [status(esa)], ['34'])).
% 0.67/0.88  thf('36', plain,
% 0.67/0.88      (((((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.88         | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))))
% 0.67/0.88         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['33', '35'])).
% 0.67/0.88  thf('37', plain,
% 0.67/0.88      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))
% 0.67/0.88         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.67/0.88      inference('simplify', [status(thm)], ['36'])).
% 0.67/0.88  thf('38', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('split', [status(esa)], ['34'])).
% 0.67/0.88  thf('39', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.88  thf('40', plain,
% 0.67/0.88      (((m1_subset_1 @ sk_C @ 
% 0.67/0.88         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['38', '39'])).
% 0.67/0.88  thf(t113_zfmisc_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.67/0.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.67/0.88  thf('41', plain,
% 0.67/0.88      (![X4 : $i, X5 : $i]:
% 0.67/0.88         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.67/0.88  thf('42', plain,
% 0.67/0.88      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['41'])).
% 0.67/0.88  thf('43', plain,
% 0.67/0.88      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['40', '42'])).
% 0.67/0.88  thf('44', plain,
% 0.67/0.88      (![X4 : $i, X5 : $i]:
% 0.67/0.88         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.67/0.88  thf('45', plain,
% 0.67/0.88      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['44'])).
% 0.67/0.88  thf(cc4_relset_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( v1_xboole_0 @ A ) =>
% 0.67/0.88       ( ![C:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.67/0.88           ( v1_xboole_0 @ C ) ) ) ))).
% 0.67/0.88  thf('46', plain,
% 0.67/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.67/0.88         (~ (v1_xboole_0 @ X14)
% 0.67/0.88          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.67/0.88          | (v1_xboole_0 @ X15))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.67/0.88  thf('47', plain,
% 0.67/0.88      (![X1 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.67/0.88          | (v1_xboole_0 @ X1)
% 0.67/0.88          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['45', '46'])).
% 0.67/0.88  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.67/0.88  thf('48', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.67/0.88  thf('49', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.67/0.88  thf('50', plain,
% 0.67/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.88  thf('51', plain, (((o_0_0_xboole_0) = (k1_xboole_0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.88  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.88      inference('demod', [status(thm)], ['48', '51'])).
% 0.67/0.88  thf('53', plain,
% 0.67/0.88      (![X1 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.67/0.88          | (v1_xboole_0 @ X1))),
% 0.67/0.88      inference('demod', [status(thm)], ['47', '52'])).
% 0.67/0.88  thf('54', plain,
% 0.67/0.88      (((v1_xboole_0 @ sk_C)) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['43', '53'])).
% 0.67/0.88  thf('55', plain,
% 0.67/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.88  thf('56', plain,
% 0.67/0.88      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('57', plain,
% 0.67/0.88      (![X30 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf('58', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('59', plain,
% 0.67/0.88      (((m1_subset_1 @ sk_C @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.67/0.88        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.88      inference('sup+', [status(thm)], ['57', '58'])).
% 0.67/0.88  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('61', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['59', '60'])).
% 0.67/0.88  thf('62', plain,
% 0.67/0.88      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['56', '61'])).
% 0.67/0.88  thf(t38_relset_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.88       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.67/0.88         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.67/0.88  thf('63', plain,
% 0.67/0.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.67/0.88         (((k8_relset_1 @ X20 @ X21 @ X22 @ X21)
% 0.67/0.88            = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.67/0.88          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.67/0.88      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.67/0.88  thf('64', plain,
% 0.67/0.88      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.88          k1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.67/0.88          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.88             k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['62', '63'])).
% 0.67/0.88  thf('65', plain,
% 0.67/0.88      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('66', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['59', '60'])).
% 0.67/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.67/0.88  thf('67', plain,
% 0.67/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.88         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.67/0.88          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.67/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.67/0.88  thf('68', plain,
% 0.67/0.88      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.88         = (k1_relat_1 @ sk_C))),
% 0.67/0.88      inference('sup-', [status(thm)], ['66', '67'])).
% 0.67/0.88  thf('69', plain,
% 0.67/0.88      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.88          k1_xboole_0) = (k1_relat_1 @ sk_C)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['65', '68'])).
% 0.67/0.88  thf('70', plain,
% 0.67/0.88      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('71', plain,
% 0.67/0.88      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.88          k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['69', '70'])).
% 0.67/0.88  thf('72', plain,
% 0.67/0.88      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('73', plain,
% 0.67/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.67/0.88        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['12', '13', '18'])).
% 0.67/0.88  thf('74', plain,
% 0.67/0.88      ((((v1_partfun1 @ k1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['72', '73'])).
% 0.67/0.88  thf('75', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('split', [status(esa)], ['34'])).
% 0.67/0.88  thf('76', plain,
% 0.67/0.88      ((((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['74', '75'])).
% 0.67/0.88  thf('77', plain,
% 0.67/0.88      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.88  thf('78', plain,
% 0.67/0.88      ((((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88         | ((u1_struct_0 @ sk_B) = (k1_xboole_0))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['76', '77'])).
% 0.67/0.88  thf('79', plain,
% 0.67/0.88      (![X26 : $i, X27 : $i]:
% 0.67/0.88         (~ (v1_partfun1 @ X27 @ X26)
% 0.67/0.88          | ((k1_relat_1 @ X27) = (X26))
% 0.67/0.88          | ~ (v4_relat_1 @ X27 @ X26)
% 0.67/0.88          | ~ (v1_relat_1 @ X27))),
% 0.67/0.88      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.67/0.88  thf('80', plain,
% 0.67/0.88      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.88         | ~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.88         | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88         | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['78', '79'])).
% 0.67/0.88  thf(dt_k2_subset_1, axiom,
% 0.67/0.88    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.67/0.88  thf('81', plain,
% 0.67/0.88      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.67/0.88  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.67/0.88  thf('82', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.67/0.88      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.67/0.88  thf('83', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.67/0.88      inference('demod', [status(thm)], ['81', '82'])).
% 0.67/0.88  thf('84', plain,
% 0.67/0.88      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['44'])).
% 0.67/0.88  thf('85', plain,
% 0.67/0.88      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.67/0.88         ((v1_relat_1 @ X8)
% 0.67/0.88          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.88  thf('86', plain,
% 0.67/0.88      (![X1 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.67/0.88          | (v1_relat_1 @ X1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.88  thf('87', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.88      inference('sup-', [status(thm)], ['83', '86'])).
% 0.67/0.88  thf('88', plain,
% 0.67/0.88      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['44'])).
% 0.67/0.88  thf('89', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.67/0.88      inference('demod', [status(thm)], ['81', '82'])).
% 0.67/0.88  thf('90', plain,
% 0.67/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.67/0.88         ((v4_relat_1 @ X11 @ X12)
% 0.67/0.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.67/0.88  thf('91', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 0.67/0.88      inference('sup-', [status(thm)], ['89', '90'])).
% 0.67/0.88  thf('92', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.67/0.88      inference('sup+', [status(thm)], ['88', '91'])).
% 0.67/0.88  thf('93', plain,
% 0.67/0.88      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.88         | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['80', '87', '92'])).
% 0.67/0.88  thf('94', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('split', [status(esa)], ['34'])).
% 0.67/0.88  thf('95', plain,
% 0.67/0.88      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.67/0.88      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.88  thf('96', plain,
% 0.67/0.88      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['94', '95'])).
% 0.67/0.88  thf('97', plain,
% 0.67/0.88      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('98', plain,
% 0.67/0.88      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['96', '97'])).
% 0.67/0.88  thf('99', plain,
% 0.67/0.88      ((((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88         | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['93', '98'])).
% 0.67/0.88  thf('100', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.67/0.88      inference('demod', [status(thm)], ['81', '82'])).
% 0.67/0.88  thf('101', plain,
% 0.67/0.88      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['44'])).
% 0.67/0.88  thf(t67_funct_2, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.67/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.67/0.88       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.67/0.88  thf('102', plain,
% 0.67/0.88      (![X28 : $i, X29 : $i]:
% 0.67/0.88         (((k1_relset_1 @ X28 @ X28 @ X29) = (X28))
% 0.67/0.88          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 0.67/0.88          | ~ (v1_funct_2 @ X29 @ X28 @ X28)
% 0.67/0.88          | ~ (v1_funct_1 @ X29))),
% 0.67/0.88      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.67/0.88  thf('103', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.67/0.88          | ~ (v1_funct_1 @ X0)
% 0.67/0.88          | ~ (v1_funct_2 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88          | ((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['101', '102'])).
% 0.67/0.88  thf('104', plain,
% 0.67/0.88      ((((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88          = (k1_xboole_0))
% 0.67/0.88        | ~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['100', '103'])).
% 0.67/0.88  thf('105', plain,
% 0.67/0.88      (((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.67/0.88         | ~ (v1_funct_1 @ k1_xboole_0)
% 0.67/0.88         | ((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88             = (k1_xboole_0))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['99', '104'])).
% 0.67/0.88  thf('106', plain,
% 0.67/0.88      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('108', plain,
% 0.67/0.88      (((v1_funct_1 @ k1_xboole_0))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['106', '107'])).
% 0.67/0.88  thf('109', plain,
% 0.67/0.88      (((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.67/0.88         | ((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88             = (k1_xboole_0))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['105', '108'])).
% 0.67/0.88  thf('110', plain,
% 0.67/0.88      (((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.67/0.88         | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['80', '87', '92'])).
% 0.67/0.88  thf('111', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('split', [status(esa)], ['34'])).
% 0.67/0.88  thf('112', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.88  thf('113', plain,
% 0.67/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.88         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.67/0.88          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.67/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.67/0.88  thf('114', plain,
% 0.67/0.88      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.88         = (k1_relat_1 @ sk_C))),
% 0.67/0.88      inference('sup-', [status(thm)], ['112', '113'])).
% 0.67/0.88  thf('115', plain,
% 0.67/0.88      ((((k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.67/0.88          = (k1_relat_1 @ sk_C)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['111', '114'])).
% 0.67/0.88  thf('116', plain,
% 0.67/0.88      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('117', plain,
% 0.67/0.88      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('118', plain,
% 0.67/0.88      ((((k1_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ k1_xboole_0)
% 0.67/0.88          = (k1_relat_1 @ k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.67/0.88  thf('119', plain,
% 0.67/0.88      (((((k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.88           = (k1_relat_1 @ k1_xboole_0))
% 0.67/0.88         | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['110', '118'])).
% 0.67/0.88  thf('120', plain,
% 0.67/0.88      (((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.67/0.88         | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.67/0.88         | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['109', '119'])).
% 0.67/0.88  thf('121', plain,
% 0.67/0.88      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('simplify', [status(thm)], ['120'])).
% 0.67/0.88  thf('122', plain,
% 0.67/0.88      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.88          k1_xboole_0) = (k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['71', '121'])).
% 0.67/0.88  thf('123', plain,
% 0.67/0.88      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.88          k1_xboole_0 @ (k2_struct_0 @ sk_B)) = (k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['64', '122'])).
% 0.67/0.88  thf('124', plain,
% 0.67/0.88      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.88  thf('125', plain,
% 0.67/0.88      (![X30 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf('126', plain,
% 0.67/0.88      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('127', plain,
% 0.67/0.88      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.67/0.88        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.88      inference('sup-', [status(thm)], ['125', '126'])).
% 0.67/0.88  thf('128', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('129', plain,
% 0.67/0.88      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['127', '128'])).
% 0.67/0.88  thf('130', plain,
% 0.67/0.88      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.88          k1_xboole_0 @ (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['124', '129'])).
% 0.67/0.88  thf('131', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('split', [status(esa)], ['34'])).
% 0.67/0.88  thf('132', plain,
% 0.67/0.88      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.88          k1_xboole_0 @ (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.67/0.88         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['130', '131'])).
% 0.67/0.88  thf('133', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.67/0.88      inference('simplify_reflect-', [status(thm)], ['123', '132'])).
% 0.67/0.88  thf('134', plain,
% 0.67/0.88      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.67/0.88       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.67/0.88      inference('split', [status(esa)], ['34'])).
% 0.67/0.88  thf('135', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.88      inference('sat_resolution*', [status(thm)], ['133', '134'])).
% 0.67/0.88  thf('136', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('simpl_trail', [status(thm)], ['37', '135'])).
% 0.67/0.88  thf('137', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['8', '136'])).
% 0.67/0.88  thf('138', plain,
% 0.67/0.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.67/0.88         (((k8_relset_1 @ X20 @ X21 @ X22 @ X21)
% 0.67/0.88            = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.67/0.88          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.67/0.88      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.67/0.88  thf('139', plain,
% 0.67/0.88      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88         (k2_struct_0 @ sk_B))
% 0.67/0.88         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.67/0.88      inference('sup-', [status(thm)], ['137', '138'])).
% 0.67/0.88  thf('140', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['6', '7'])).
% 0.67/0.88  thf('141', plain,
% 0.67/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.88         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.67/0.88          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.67/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.67/0.88  thf('142', plain,
% 0.67/0.88      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.88         = (k1_relat_1 @ sk_C))),
% 0.67/0.88      inference('sup-', [status(thm)], ['140', '141'])).
% 0.67/0.88  thf('143', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('simpl_trail', [status(thm)], ['37', '135'])).
% 0.67/0.88  thf('144', plain,
% 0.67/0.88      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.67/0.88         = (k1_relat_1 @ sk_C))),
% 0.67/0.88      inference('demod', [status(thm)], ['142', '143'])).
% 0.67/0.88  thf('145', plain,
% 0.67/0.88      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88         (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.67/0.88      inference('demod', [status(thm)], ['139', '144'])).
% 0.67/0.88  thf('146', plain,
% 0.67/0.88      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))
% 0.67/0.88         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.67/0.88      inference('simplify', [status(thm)], ['36'])).
% 0.67/0.88  thf('147', plain,
% 0.67/0.88      (![X30 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf('148', plain,
% 0.67/0.88      (![X30 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf('149', plain,
% 0.67/0.88      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('150', plain,
% 0.67/0.88      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.67/0.88        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['148', '149'])).
% 0.67/0.88  thf('151', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('152', plain,
% 0.67/0.88      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['150', '151'])).
% 0.67/0.88  thf('153', plain,
% 0.67/0.88      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.67/0.88        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.88      inference('sup-', [status(thm)], ['147', '152'])).
% 0.67/0.88  thf('154', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('155', plain,
% 0.67/0.88      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['153', '154'])).
% 0.67/0.88  thf('156', plain,
% 0.67/0.88      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.67/0.88         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['146', '155'])).
% 0.67/0.88  thf('157', plain,
% 0.67/0.88      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))
% 0.67/0.88         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.67/0.88      inference('simplify', [status(thm)], ['36'])).
% 0.67/0.88  thf('158', plain,
% 0.67/0.88      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88          (k2_struct_0 @ sk_B)) != (k1_relat_1 @ sk_C)))
% 0.67/0.88         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['156', '157'])).
% 0.67/0.88  thf('159', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.67/0.88      inference('sat_resolution*', [status(thm)], ['133', '134'])).
% 0.67/0.88  thf('160', plain,
% 0.67/0.88      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.67/0.88         (k2_struct_0 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.67/0.88      inference('simpl_trail', [status(thm)], ['158', '159'])).
% 0.67/0.88  thf('161', plain, ($false),
% 0.67/0.88      inference('simplify_reflect-', [status(thm)], ['145', '160'])).
% 0.67/0.88  
% 0.67/0.88  % SZS output end Refutation
% 0.67/0.88  
% 0.67/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
