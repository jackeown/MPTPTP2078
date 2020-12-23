%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0dacYku1kW

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:59 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  326 (9438 expanded)
%              Number of leaves         :   48 (2716 expanded)
%              Depth                    :   36
%              Number of atoms          : 2905 (233010 expanded)
%              Number of equality atoms :  175 (11691 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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

thf('6',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','33'])).

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
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','38'])).

thf('40',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','53'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X32 @ X33 @ X34 ) @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','64'])).

thf('66',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','53'])).

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

thf('68',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X29 @ X31 )
       != X29 )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_tops_2 @ X30 @ X29 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('74',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('75',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('77',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','77'])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','83'])).

thf('85',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('89',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('94',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','53'])).

thf('98',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X32 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('102',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['82'])).

thf('104',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['96','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('110',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('114',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['113','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('120',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','53'])).

thf('124',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X32 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('128',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['122','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('131',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('135',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X29 @ X31 )
       != X29 )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_tops_2 @ X30 @ X29 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('143',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('146',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('147',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('151',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('153',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('156',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('157',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['155','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('166',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('168',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','144','153','154','168'])).

thf('170',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['132','170'])).

thf('172',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','83'])).

thf('173',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','171','172'])).

thf('174',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('175',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('178',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('180',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('182',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('183',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('184',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('185',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('186',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('187',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('189',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('192',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != X25 )
      | ( v1_partfun1 @ X26 @ X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('193',plain,(
    ! [X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v4_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
      | ( v1_partfun1 @ X26 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['191','193'])).

thf('195',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['190','194'])).

thf('196',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('200',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','196','197','198','199'])).

thf('201',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['184','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['201','202','203','204'])).

thf('206',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('207',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('209',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('210',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['175','180','183','210'])).

thf('212',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('213',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('215',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('217',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('219',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('220',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['220'])).

thf('222',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','221'])).

thf('223',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['218','224'])).

thf('226',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('229',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('230',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['227','228','229'])).

thf('231',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['217','230'])).

thf('232',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('233',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','38'])).

thf('234',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('235',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('237',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('239',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['235','236','239'])).

thf('241',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('242',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['231','232','240','241'])).

thf('243',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('244',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('245',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('246',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('248',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('249',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('250',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('251',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['220'])).

thf('252',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['249','254'])).

thf('256',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['248','257'])).

thf('259',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('260',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['235','236','239'])).

thf('262',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['235','236','239'])).

thf('263',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('264',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['260','261','262','263'])).

thf('265',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['247','264'])).

thf('266',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['246','265'])).

thf('267',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['243','266'])).

thf('268',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('269',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['267','268','269','270'])).

thf('272',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['220'])).

thf('274',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['272','273'])).

thf('275',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['242','274'])).

thf('276',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','275'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0dacYku1kW
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:29:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.03/1.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.22  % Solved by: fo/fo7.sh
% 1.03/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.22  % done 673 iterations in 0.793s
% 1.03/1.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.22  % SZS output start Refutation
% 1.03/1.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.22  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.03/1.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.03/1.22  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.03/1.22  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.03/1.22  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.03/1.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.03/1.22  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.03/1.22  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.03/1.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.22  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.03/1.22  thf(sk_C_type, type, sk_C: $i).
% 1.03/1.22  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.03/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.22  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.03/1.22  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.03/1.22  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.03/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.22  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.03/1.22  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.03/1.22  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.03/1.22  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.03/1.22  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.03/1.22  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.03/1.22  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.03/1.22  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.03/1.22  thf(d3_struct_0, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.03/1.22  thf('0', plain,
% 1.03/1.22      (![X27 : $i]:
% 1.03/1.22         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.22      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.22  thf('1', plain,
% 1.03/1.22      (![X27 : $i]:
% 1.03/1.22         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.22      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.22  thf(t62_tops_2, conjecture,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( l1_struct_0 @ A ) =>
% 1.03/1.22       ( ![B:$i]:
% 1.03/1.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.03/1.22           ( ![C:$i]:
% 1.03/1.22             ( ( ( v1_funct_1 @ C ) & 
% 1.03/1.22                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.03/1.22                 ( m1_subset_1 @
% 1.03/1.22                   C @ 
% 1.03/1.22                   ( k1_zfmisc_1 @
% 1.03/1.22                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.03/1.22               ( ( ( ( k2_relset_1 @
% 1.03/1.22                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.03/1.22                     ( k2_struct_0 @ B ) ) & 
% 1.03/1.22                   ( v2_funct_1 @ C ) ) =>
% 1.03/1.22                 ( ( ( k1_relset_1 @
% 1.03/1.22                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.03/1.22                       ( k2_tops_2 @
% 1.03/1.22                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.03/1.22                     ( k2_struct_0 @ B ) ) & 
% 1.03/1.22                   ( ( k2_relset_1 @
% 1.03/1.22                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.03/1.22                       ( k2_tops_2 @
% 1.03/1.22                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.03/1.22                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.03/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.22    (~( ![A:$i]:
% 1.03/1.22        ( ( l1_struct_0 @ A ) =>
% 1.03/1.22          ( ![B:$i]:
% 1.03/1.22            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.03/1.22              ( ![C:$i]:
% 1.03/1.22                ( ( ( v1_funct_1 @ C ) & 
% 1.03/1.22                    ( v1_funct_2 @
% 1.03/1.22                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.03/1.22                    ( m1_subset_1 @
% 1.03/1.22                      C @ 
% 1.03/1.22                      ( k1_zfmisc_1 @
% 1.03/1.22                        ( k2_zfmisc_1 @
% 1.03/1.22                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.03/1.22                  ( ( ( ( k2_relset_1 @
% 1.03/1.22                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.03/1.22                        ( k2_struct_0 @ B ) ) & 
% 1.03/1.22                      ( v2_funct_1 @ C ) ) =>
% 1.03/1.22                    ( ( ( k1_relset_1 @
% 1.03/1.22                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.03/1.22                          ( k2_tops_2 @
% 1.03/1.22                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.03/1.22                        ( k2_struct_0 @ B ) ) & 
% 1.03/1.22                      ( ( k2_relset_1 @
% 1.03/1.22                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.03/1.22                          ( k2_tops_2 @
% 1.03/1.22                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.03/1.22                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.03/1.22    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.03/1.22  thf('2', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C @ 
% 1.03/1.22        (k1_zfmisc_1 @ 
% 1.03/1.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('3', plain,
% 1.03/1.22      (((m1_subset_1 @ sk_C @ 
% 1.03/1.22         (k1_zfmisc_1 @ 
% 1.03/1.22          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.03/1.22        | ~ (l1_struct_0 @ sk_A))),
% 1.03/1.22      inference('sup+', [status(thm)], ['1', '2'])).
% 1.03/1.22  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('5', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C @ 
% 1.03/1.22        (k1_zfmisc_1 @ 
% 1.03/1.22         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.22      inference('demod', [status(thm)], ['3', '4'])).
% 1.03/1.22  thf('6', plain,
% 1.03/1.22      (![X27 : $i]:
% 1.03/1.22         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.22      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.22  thf('7', plain,
% 1.03/1.22      (![X27 : $i]:
% 1.03/1.22         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.22      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.22  thf('8', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C @ 
% 1.03/1.22        (k1_zfmisc_1 @ 
% 1.03/1.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('9', plain,
% 1.03/1.22      (((m1_subset_1 @ sk_C @ 
% 1.03/1.22         (k1_zfmisc_1 @ 
% 1.03/1.22          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.03/1.22        | ~ (l1_struct_0 @ sk_B))),
% 1.03/1.22      inference('sup+', [status(thm)], ['7', '8'])).
% 1.03/1.22  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('11', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C @ 
% 1.03/1.22        (k1_zfmisc_1 @ 
% 1.03/1.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.03/1.22      inference('demod', [status(thm)], ['9', '10'])).
% 1.03/1.22  thf('12', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C @ 
% 1.03/1.22        (k1_zfmisc_1 @ 
% 1.03/1.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(redefinition_k2_relset_1, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.03/1.22  thf('13', plain,
% 1.03/1.22      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.03/1.22         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.03/1.22          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.22  thf('14', plain,
% 1.03/1.22      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.22         = (k2_relat_1 @ sk_C))),
% 1.03/1.22      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.22  thf('15', plain,
% 1.03/1.22      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.22         = (k2_struct_0 @ sk_B))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.22      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.22  thf('17', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_C @ 
% 1.03/1.22        (k1_zfmisc_1 @ 
% 1.03/1.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.03/1.22      inference('demod', [status(thm)], ['11', '16'])).
% 1.03/1.22  thf(cc5_funct_2, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.03/1.22       ( ![C:$i]:
% 1.03/1.22         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.03/1.22             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.03/1.22  thf('18', plain,
% 1.03/1.22      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.03/1.22         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.03/1.22          | (v1_partfun1 @ X14 @ X15)
% 1.03/1.22          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 1.03/1.22          | ~ (v1_funct_1 @ X14)
% 1.03/1.22          | (v1_xboole_0 @ X16))),
% 1.03/1.22      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.03/1.22  thf('19', plain,
% 1.03/1.22      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.03/1.22        | ~ (v1_funct_1 @ sk_C)
% 1.03/1.22        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.03/1.22        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['17', '18'])).
% 1.03/1.22  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('21', plain,
% 1.03/1.22      (![X27 : $i]:
% 1.03/1.22         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.22      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.22  thf('22', plain,
% 1.03/1.22      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('23', plain,
% 1.03/1.22      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.03/1.22        | ~ (l1_struct_0 @ sk_B))),
% 1.03/1.22      inference('sup+', [status(thm)], ['21', '22'])).
% 1.03/1.22  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('25', plain,
% 1.03/1.22      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.03/1.22      inference('demod', [status(thm)], ['23', '24'])).
% 1.03/1.22  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.22      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.22  thf('27', plain,
% 1.03/1.22      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.03/1.22      inference('demod', [status(thm)], ['25', '26'])).
% 1.03/1.22  thf('28', plain,
% 1.03/1.22      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.03/1.22        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.03/1.22      inference('demod', [status(thm)], ['19', '20', '27'])).
% 1.03/1.22  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.22      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.22  thf('30', plain,
% 1.03/1.22      (![X27 : $i]:
% 1.03/1.22         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.22      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.22  thf(fc2_struct_0, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.03/1.22       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.03/1.22  thf('31', plain,
% 1.03/1.22      (![X28 : $i]:
% 1.03/1.22         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 1.03/1.22          | ~ (l1_struct_0 @ X28)
% 1.03/1.22          | (v2_struct_0 @ X28))),
% 1.03/1.22      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.03/1.22  thf('32', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.03/1.22          | ~ (l1_struct_0 @ X0)
% 1.03/1.22          | (v2_struct_0 @ X0)
% 1.03/1.22          | ~ (l1_struct_0 @ X0))),
% 1.03/1.22      inference('sup-', [status(thm)], ['30', '31'])).
% 1.03/1.22  thf('33', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((v2_struct_0 @ X0)
% 1.03/1.22          | ~ (l1_struct_0 @ X0)
% 1.03/1.22          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.03/1.22      inference('simplify', [status(thm)], ['32'])).
% 1.03/1.22  thf('34', plain,
% 1.03/1.22      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.03/1.22        | ~ (l1_struct_0 @ sk_B)
% 1.03/1.22        | (v2_struct_0 @ sk_B))),
% 1.03/1.22      inference('sup-', [status(thm)], ['29', '33'])).
% 1.03/1.22  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('36', plain,
% 1.03/1.22      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.03/1.22      inference('demod', [status(thm)], ['34', '35'])).
% 1.03/1.23  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('38', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('clc', [status(thm)], ['36', '37'])).
% 1.03/1.23  thf('39', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.03/1.23      inference('clc', [status(thm)], ['28', '38'])).
% 1.03/1.23  thf('40', plain,
% 1.03/1.23      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.03/1.23      inference('sup+', [status(thm)], ['6', '39'])).
% 1.03/1.23  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('42', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['40', '41'])).
% 1.03/1.23  thf(d4_partfun1, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.03/1.23       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.03/1.23  thf('43', plain,
% 1.03/1.23      (![X25 : $i, X26 : $i]:
% 1.03/1.23         (~ (v1_partfun1 @ X26 @ X25)
% 1.03/1.23          | ((k1_relat_1 @ X26) = (X25))
% 1.03/1.23          | ~ (v4_relat_1 @ X26 @ X25)
% 1.03/1.23          | ~ (v1_relat_1 @ X26))),
% 1.03/1.23      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.03/1.23  thf('44', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ sk_C)
% 1.03/1.23        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.03/1.23        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['42', '43'])).
% 1.03/1.23  thf('45', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf(cc2_relat_1, axiom,
% 1.03/1.23    (![A:$i]:
% 1.03/1.23     ( ( v1_relat_1 @ A ) =>
% 1.03/1.23       ( ![B:$i]:
% 1.03/1.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.03/1.23  thf('46', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.03/1.23          | (v1_relat_1 @ X0)
% 1.03/1.23          | ~ (v1_relat_1 @ X1))),
% 1.03/1.23      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.03/1.23  thf('47', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ 
% 1.03/1.23           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.03/1.23        | (v1_relat_1 @ sk_C))),
% 1.03/1.23      inference('sup-', [status(thm)], ['45', '46'])).
% 1.03/1.23  thf(fc6_relat_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.03/1.23  thf('48', plain,
% 1.03/1.23      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.03/1.23      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.03/1.23  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.23      inference('demod', [status(thm)], ['47', '48'])).
% 1.03/1.23  thf('50', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['3', '4'])).
% 1.03/1.23  thf(cc2_relset_1, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.23       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.03/1.23  thf('51', plain,
% 1.03/1.23      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.03/1.23         ((v4_relat_1 @ X8 @ X9)
% 1.03/1.23          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.03/1.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.03/1.23  thf('52', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('sup-', [status(thm)], ['50', '51'])).
% 1.03/1.23  thf('53', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.03/1.23  thf('54', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['5', '53'])).
% 1.03/1.23  thf(dt_k2_tops_2, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.03/1.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.23       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 1.03/1.23         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 1.03/1.23         ( m1_subset_1 @
% 1.03/1.23           ( k2_tops_2 @ A @ B @ C ) @ 
% 1.03/1.23           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 1.03/1.23  thf('55', plain,
% 1.03/1.23      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.03/1.23         ((v1_funct_2 @ (k2_tops_2 @ X32 @ X33 @ X34) @ X33 @ X32)
% 1.03/1.23          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.03/1.23          | ~ (v1_funct_2 @ X34 @ X32 @ X33)
% 1.03/1.23          | ~ (v1_funct_1 @ X34))),
% 1.03/1.23      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.03/1.23  thf('56', plain,
% 1.03/1.23      ((~ (v1_funct_1 @ sk_C)
% 1.03/1.23        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.03/1.23        | (v1_funct_2 @ 
% 1.03/1.23           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.03/1.23           (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['54', '55'])).
% 1.03/1.23  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('58', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('59', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('60', plain,
% 1.03/1.23      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_A))),
% 1.03/1.23      inference('sup+', [status(thm)], ['58', '59'])).
% 1.03/1.23  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('62', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('demod', [status(thm)], ['60', '61'])).
% 1.03/1.23  thf('63', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.03/1.23  thf('64', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('demod', [status(thm)], ['62', '63'])).
% 1.03/1.23  thf('65', plain,
% 1.03/1.23      ((v1_funct_2 @ 
% 1.03/1.23        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.03/1.23        (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['56', '57', '64'])).
% 1.03/1.23  thf('66', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('67', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['5', '53'])).
% 1.03/1.23  thf(d4_tops_2, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.03/1.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.23       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.03/1.23         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.03/1.23  thf('68', plain,
% 1.03/1.23      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.03/1.23         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 1.03/1.23          | ~ (v2_funct_1 @ X31)
% 1.03/1.23          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 1.03/1.23          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 1.03/1.23          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 1.03/1.23          | ~ (v1_funct_1 @ X31))),
% 1.03/1.23      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.03/1.23  thf('69', plain,
% 1.03/1.23      ((~ (v1_funct_1 @ sk_C)
% 1.03/1.23        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.03/1.23        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23            = (k2_funct_1 @ sk_C))
% 1.03/1.23        | ~ (v2_funct_1 @ sk_C)
% 1.03/1.23        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23            != (u1_struct_0 @ sk_B)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['67', '68'])).
% 1.03/1.23  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('71', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('demod', [status(thm)], ['62', '63'])).
% 1.03/1.23  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('73', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['3', '4'])).
% 1.03/1.23  thf('74', plain,
% 1.03/1.23      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.03/1.23         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.03/1.23          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.03/1.23      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.23  thf('75', plain,
% 1.03/1.23      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23         = (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('sup-', [status(thm)], ['73', '74'])).
% 1.03/1.23  thf('76', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.03/1.23  thf('77', plain,
% 1.03/1.23      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23         = (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['75', '76'])).
% 1.03/1.23  thf('78', plain,
% 1.03/1.23      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23          = (k2_funct_1 @ sk_C))
% 1.03/1.23        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.03/1.23      inference('demod', [status(thm)], ['69', '70', '71', '72', '77'])).
% 1.03/1.23  thf('79', plain,
% 1.03/1.23      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_B)
% 1.03/1.23        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23            = (k2_funct_1 @ sk_C)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['66', '78'])).
% 1.03/1.23  thf('80', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('82', plain,
% 1.03/1.23      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.03/1.23        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23            = (k2_funct_1 @ sk_C)))),
% 1.03/1.23      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.03/1.23  thf('83', plain,
% 1.03/1.23      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23         = (k2_funct_1 @ sk_C))),
% 1.03/1.23      inference('simplify', [status(thm)], ['82'])).
% 1.03/1.23  thf('84', plain,
% 1.03/1.23      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.03/1.23        (k1_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['65', '83'])).
% 1.03/1.23  thf('85', plain,
% 1.03/1.23      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 1.03/1.23         (k1_relat_1 @ sk_C))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['0', '84'])).
% 1.03/1.23  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('88', plain,
% 1.03/1.23      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.03/1.23        (k1_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.03/1.23  thf(d1_funct_2, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.23       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.23           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.03/1.23             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.03/1.23         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.23           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.03/1.23             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.03/1.23  thf(zf_stmt_1, axiom,
% 1.03/1.23    (![C:$i,B:$i,A:$i]:
% 1.03/1.23     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.03/1.23       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.03/1.23  thf('89', plain,
% 1.03/1.23      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.03/1.23         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.03/1.23          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.03/1.23          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.03/1.23  thf('90', plain,
% 1.03/1.23      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23           (k2_relat_1 @ sk_C))
% 1.03/1.23        | ((k2_relat_1 @ sk_C)
% 1.03/1.23            = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23               (k2_funct_1 @ sk_C))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['88', '89'])).
% 1.03/1.23  thf(zf_stmt_2, axiom,
% 1.03/1.23    (![B:$i,A:$i]:
% 1.03/1.23     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.23       ( zip_tseitin_0 @ B @ A ) ))).
% 1.03/1.23  thf('91', plain,
% 1.03/1.23      (![X17 : $i, X18 : $i]:
% 1.03/1.23         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.03/1.23  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.03/1.23  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.23  thf('93', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.03/1.23      inference('sup+', [status(thm)], ['91', '92'])).
% 1.03/1.23  thf(fc8_relat_1, axiom,
% 1.03/1.23    (![A:$i]:
% 1.03/1.23     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.03/1.23       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 1.03/1.23  thf('94', plain,
% 1.03/1.23      (![X5 : $i]:
% 1.03/1.23         (~ (v1_xboole_0 @ (k1_relat_1 @ X5))
% 1.03/1.23          | ~ (v1_relat_1 @ X5)
% 1.03/1.23          | (v1_xboole_0 @ X5))),
% 1.03/1.23      inference('cnf', [status(esa)], [fc8_relat_1])).
% 1.03/1.23  thf('95', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         ((zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.03/1.23          | (v1_xboole_0 @ X0)
% 1.03/1.23          | ~ (v1_relat_1 @ X0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['93', '94'])).
% 1.03/1.23  thf('96', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('97', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['5', '53'])).
% 1.03/1.23  thf('98', plain,
% 1.03/1.23      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.03/1.23         ((m1_subset_1 @ (k2_tops_2 @ X32 @ X33 @ X34) @ 
% 1.03/1.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.03/1.23          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.03/1.23          | ~ (v1_funct_2 @ X34 @ X32 @ X33)
% 1.03/1.23          | ~ (v1_funct_1 @ X34))),
% 1.03/1.23      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.03/1.23  thf('99', plain,
% 1.03/1.23      ((~ (v1_funct_1 @ sk_C)
% 1.03/1.23        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.03/1.23        | (m1_subset_1 @ 
% 1.03/1.23           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.03/1.23           (k1_zfmisc_1 @ 
% 1.03/1.23            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['97', '98'])).
% 1.03/1.23  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('101', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('demod', [status(thm)], ['62', '63'])).
% 1.03/1.23  thf('102', plain,
% 1.03/1.23      ((m1_subset_1 @ 
% 1.03/1.23        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.03/1.23      inference('demod', [status(thm)], ['99', '100', '101'])).
% 1.03/1.23  thf('103', plain,
% 1.03/1.23      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23         = (k2_funct_1 @ sk_C))),
% 1.03/1.23      inference('simplify', [status(thm)], ['82'])).
% 1.03/1.23  thf('104', plain,
% 1.03/1.23      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.03/1.23      inference('demod', [status(thm)], ['102', '103'])).
% 1.03/1.23  thf('105', plain,
% 1.03/1.23      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.23         (k1_zfmisc_1 @ 
% 1.03/1.23          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['96', '104'])).
% 1.03/1.23  thf('106', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('108', plain,
% 1.03/1.23      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.03/1.23      inference('demod', [status(thm)], ['105', '106', '107'])).
% 1.03/1.23  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.03/1.23  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.03/1.23  thf(zf_stmt_5, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.23       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.03/1.23         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.23           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.03/1.23             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.03/1.23  thf('109', plain,
% 1.03/1.23      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.03/1.23         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.03/1.23          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.03/1.23          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.03/1.23  thf('110', plain,
% 1.03/1.23      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23         (k2_relat_1 @ sk_C))
% 1.03/1.23        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['108', '109'])).
% 1.03/1.23  thf('111', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ sk_C)
% 1.03/1.23        | (v1_xboole_0 @ sk_C)
% 1.03/1.23        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23           (k2_relat_1 @ sk_C)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['95', '110'])).
% 1.03/1.23  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.23      inference('demod', [status(thm)], ['47', '48'])).
% 1.03/1.23  thf('113', plain,
% 1.03/1.23      (((v1_xboole_0 @ sk_C)
% 1.03/1.23        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23           (k2_relat_1 @ sk_C)))),
% 1.03/1.23      inference('demod', [status(thm)], ['111', '112'])).
% 1.03/1.23  thf(fc11_relat_1, axiom,
% 1.03/1.23    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 1.03/1.23  thf('114', plain,
% 1.03/1.23      (![X2 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X2)) | ~ (v1_xboole_0 @ X2))),
% 1.03/1.23      inference('cnf', [status(esa)], [fc11_relat_1])).
% 1.03/1.23  thf('115', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('clc', [status(thm)], ['36', '37'])).
% 1.03/1.23  thf('116', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.03/1.23      inference('sup-', [status(thm)], ['114', '115'])).
% 1.03/1.23  thf('117', plain,
% 1.03/1.23      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23        (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('clc', [status(thm)], ['113', '116'])).
% 1.03/1.23  thf('118', plain,
% 1.03/1.23      (((k2_relat_1 @ sk_C)
% 1.03/1.23         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23            (k2_funct_1 @ sk_C)))),
% 1.03/1.23      inference('demod', [status(thm)], ['90', '117'])).
% 1.03/1.23  thf('119', plain,
% 1.03/1.23      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.03/1.23      inference('demod', [status(thm)], ['102', '103'])).
% 1.03/1.23  thf('120', plain,
% 1.03/1.23      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.03/1.23         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.03/1.23          | (v1_partfun1 @ X14 @ X15)
% 1.03/1.23          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 1.03/1.23          | ~ (v1_funct_1 @ X14)
% 1.03/1.23          | (v1_xboole_0 @ X16))),
% 1.03/1.23      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.03/1.23  thf('121', plain,
% 1.03/1.23      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.03/1.23        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.03/1.23        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.03/1.23             (k1_relat_1 @ sk_C))
% 1.03/1.23        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['119', '120'])).
% 1.03/1.23  thf('122', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('123', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['5', '53'])).
% 1.03/1.23  thf('124', plain,
% 1.03/1.23      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.03/1.23         ((v1_funct_1 @ (k2_tops_2 @ X32 @ X33 @ X34))
% 1.03/1.23          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.03/1.23          | ~ (v1_funct_2 @ X34 @ X32 @ X33)
% 1.03/1.23          | ~ (v1_funct_1 @ X34))),
% 1.03/1.23      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.03/1.23  thf('125', plain,
% 1.03/1.23      ((~ (v1_funct_1 @ sk_C)
% 1.03/1.23        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.03/1.23        | (v1_funct_1 @ 
% 1.03/1.23           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['123', '124'])).
% 1.03/1.23  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('127', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('demod', [status(thm)], ['62', '63'])).
% 1.03/1.23  thf('128', plain,
% 1.03/1.23      ((v1_funct_1 @ 
% 1.03/1.23        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['125', '126', '127'])).
% 1.03/1.23  thf('129', plain,
% 1.03/1.23      (((v1_funct_1 @ 
% 1.03/1.23         (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['122', '128'])).
% 1.03/1.23  thf('130', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('131', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('132', plain,
% 1.03/1.23      ((v1_funct_1 @ 
% 1.03/1.23        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.03/1.23  thf('133', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('134', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['3', '4'])).
% 1.03/1.23  thf('135', plain,
% 1.03/1.23      (((m1_subset_1 @ sk_C @ 
% 1.03/1.23         (k1_zfmisc_1 @ 
% 1.03/1.23          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['133', '134'])).
% 1.03/1.23  thf('136', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('137', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['135', '136'])).
% 1.03/1.23  thf('138', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('139', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.03/1.23      inference('demod', [status(thm)], ['137', '138'])).
% 1.03/1.23  thf('140', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.03/1.23  thf('141', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.03/1.23      inference('demod', [status(thm)], ['139', '140'])).
% 1.03/1.23  thf('142', plain,
% 1.03/1.23      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.03/1.23         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 1.03/1.23          | ~ (v2_funct_1 @ X31)
% 1.03/1.23          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 1.03/1.23          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 1.03/1.23          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 1.03/1.23          | ~ (v1_funct_1 @ X31))),
% 1.03/1.23      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.03/1.23  thf('143', plain,
% 1.03/1.23      ((~ (v1_funct_1 @ sk_C)
% 1.03/1.23        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.03/1.23        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.03/1.23            = (k2_funct_1 @ sk_C))
% 1.03/1.23        | ~ (v2_funct_1 @ sk_C)
% 1.03/1.23        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.03/1.23            != (k2_relat_1 @ sk_C)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['141', '142'])).
% 1.03/1.23  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('145', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('146', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('demod', [status(thm)], ['60', '61'])).
% 1.03/1.23  thf('147', plain,
% 1.03/1.23      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['145', '146'])).
% 1.03/1.23  thf('148', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('149', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('demod', [status(thm)], ['147', '148'])).
% 1.03/1.23  thf('150', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('151', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['149', '150'])).
% 1.03/1.23  thf('152', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.03/1.23  thf('153', plain,
% 1.03/1.23      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['151', '152'])).
% 1.03/1.23  thf('154', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('155', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('156', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('157', plain,
% 1.03/1.23      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23         = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('158', plain,
% 1.03/1.23      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23          = (k2_struct_0 @ sk_B))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_A))),
% 1.03/1.23      inference('sup+', [status(thm)], ['156', '157'])).
% 1.03/1.23  thf('159', plain, ((l1_struct_0 @ sk_A)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('160', plain,
% 1.03/1.23      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23         = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('demod', [status(thm)], ['158', '159'])).
% 1.03/1.23  thf('161', plain,
% 1.03/1.23      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23          = (k2_struct_0 @ sk_B))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['155', '160'])).
% 1.03/1.23  thf('162', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('163', plain,
% 1.03/1.23      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.03/1.23         = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('demod', [status(thm)], ['161', '162'])).
% 1.03/1.23  thf('164', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('165', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('166', plain,
% 1.03/1.23      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.03/1.23         = (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['163', '164', '165'])).
% 1.03/1.23  thf('167', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.03/1.23  thf('168', plain,
% 1.03/1.23      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.03/1.23         = (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['166', '167'])).
% 1.03/1.23  thf('169', plain,
% 1.03/1.23      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.03/1.23          = (k2_funct_1 @ sk_C))
% 1.03/1.23        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.03/1.23      inference('demod', [status(thm)], ['143', '144', '153', '154', '168'])).
% 1.03/1.23  thf('170', plain,
% 1.03/1.23      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.03/1.23         = (k2_funct_1 @ sk_C))),
% 1.03/1.23      inference('simplify', [status(thm)], ['169'])).
% 1.03/1.23  thf('171', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['132', '170'])).
% 1.03/1.23  thf('172', plain,
% 1.03/1.23      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.03/1.23        (k1_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['65', '83'])).
% 1.03/1.23  thf('173', plain,
% 1.03/1.23      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.03/1.23        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.03/1.23      inference('demod', [status(thm)], ['121', '171', '172'])).
% 1.03/1.23  thf('174', plain,
% 1.03/1.23      (![X25 : $i, X26 : $i]:
% 1.03/1.23         (~ (v1_partfun1 @ X26 @ X25)
% 1.03/1.23          | ((k1_relat_1 @ X26) = (X25))
% 1.03/1.23          | ~ (v4_relat_1 @ X26 @ X25)
% 1.03/1.23          | ~ (v1_relat_1 @ X26))),
% 1.03/1.23      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.03/1.23  thf('175', plain,
% 1.03/1.23      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.03/1.23        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.03/1.23        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.03/1.23        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['173', '174'])).
% 1.03/1.23  thf('176', plain,
% 1.03/1.23      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.03/1.23      inference('demod', [status(thm)], ['102', '103'])).
% 1.03/1.23  thf('177', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.03/1.23          | (v1_relat_1 @ X0)
% 1.03/1.23          | ~ (v1_relat_1 @ X1))),
% 1.03/1.23      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.03/1.23  thf('178', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ 
% 1.03/1.23           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))
% 1.03/1.23        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['176', '177'])).
% 1.03/1.23  thf('179', plain,
% 1.03/1.23      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.03/1.23      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.03/1.23  thf('180', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['178', '179'])).
% 1.03/1.23  thf('181', plain,
% 1.03/1.23      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.03/1.23      inference('demod', [status(thm)], ['102', '103'])).
% 1.03/1.23  thf('182', plain,
% 1.03/1.23      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.03/1.23         ((v4_relat_1 @ X8 @ X9)
% 1.03/1.23          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.03/1.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.03/1.23  thf('183', plain,
% 1.03/1.23      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup-', [status(thm)], ['181', '182'])).
% 1.03/1.23  thf(t55_funct_1, axiom,
% 1.03/1.23    (![A:$i]:
% 1.03/1.23     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.03/1.23       ( ( v2_funct_1 @ A ) =>
% 1.03/1.23         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.03/1.23           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.03/1.23  thf('184', plain,
% 1.03/1.23      (![X7 : $i]:
% 1.03/1.23         (~ (v2_funct_1 @ X7)
% 1.03/1.23          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 1.03/1.23          | ~ (v1_funct_1 @ X7)
% 1.03/1.23          | ~ (v1_relat_1 @ X7))),
% 1.03/1.23      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.03/1.23  thf('185', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('186', plain,
% 1.03/1.23      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup-', [status(thm)], ['181', '182'])).
% 1.03/1.23  thf('187', plain,
% 1.03/1.23      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 1.03/1.23        | ~ (l1_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['185', '186'])).
% 1.03/1.23  thf('188', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('189', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('190', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['187', '188', '189'])).
% 1.03/1.23  thf('191', plain,
% 1.03/1.23      (![X7 : $i]:
% 1.03/1.23         (~ (v2_funct_1 @ X7)
% 1.03/1.23          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 1.03/1.23          | ~ (v1_funct_1 @ X7)
% 1.03/1.23          | ~ (v1_relat_1 @ X7))),
% 1.03/1.23      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.03/1.23  thf('192', plain,
% 1.03/1.23      (![X25 : $i, X26 : $i]:
% 1.03/1.23         (((k1_relat_1 @ X26) != (X25))
% 1.03/1.23          | (v1_partfun1 @ X26 @ X25)
% 1.03/1.23          | ~ (v4_relat_1 @ X26 @ X25)
% 1.03/1.23          | ~ (v1_relat_1 @ X26))),
% 1.03/1.23      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.03/1.23  thf('193', plain,
% 1.03/1.23      (![X26 : $i]:
% 1.03/1.23         (~ (v1_relat_1 @ X26)
% 1.03/1.23          | ~ (v4_relat_1 @ X26 @ (k1_relat_1 @ X26))
% 1.03/1.23          | (v1_partfun1 @ X26 @ (k1_relat_1 @ X26)))),
% 1.03/1.23      inference('simplify', [status(thm)], ['192'])).
% 1.03/1.23  thf('194', plain,
% 1.03/1.23      (![X0 : $i]:
% 1.03/1.23         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.03/1.23          | ~ (v1_relat_1 @ X0)
% 1.03/1.23          | ~ (v1_funct_1 @ X0)
% 1.03/1.23          | ~ (v2_funct_1 @ X0)
% 1.03/1.23          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.03/1.23          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['191', '193'])).
% 1.03/1.23  thf('195', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.03/1.23        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.23           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.03/1.23        | ~ (v2_funct_1 @ sk_C)
% 1.03/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.03/1.23        | ~ (v1_relat_1 @ sk_C))),
% 1.03/1.23      inference('sup-', [status(thm)], ['190', '194'])).
% 1.03/1.23  thf('196', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['178', '179'])).
% 1.03/1.23  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.23      inference('demod', [status(thm)], ['47', '48'])).
% 1.03/1.23  thf('200', plain,
% 1.03/1.23      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.03/1.23      inference('demod', [status(thm)], ['195', '196', '197', '198', '199'])).
% 1.03/1.23  thf('201', plain,
% 1.03/1.23      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.03/1.23        | ~ (v1_relat_1 @ sk_C)
% 1.03/1.23        | ~ (v1_funct_1 @ sk_C)
% 1.03/1.23        | ~ (v2_funct_1 @ sk_C))),
% 1.03/1.23      inference('sup+', [status(thm)], ['184', '200'])).
% 1.03/1.23  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.23      inference('demod', [status(thm)], ['47', '48'])).
% 1.03/1.23  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('204', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('205', plain,
% 1.03/1.23      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['201', '202', '203', '204'])).
% 1.03/1.23  thf('206', plain,
% 1.03/1.23      (![X25 : $i, X26 : $i]:
% 1.03/1.23         (~ (v1_partfun1 @ X26 @ X25)
% 1.03/1.23          | ((k1_relat_1 @ X26) = (X25))
% 1.03/1.23          | ~ (v4_relat_1 @ X26 @ X25)
% 1.03/1.23          | ~ (v1_relat_1 @ X26))),
% 1.03/1.23      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.03/1.23  thf('207', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.03/1.23        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.03/1.23        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['205', '206'])).
% 1.03/1.23  thf('208', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['178', '179'])).
% 1.03/1.23  thf('209', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['187', '188', '189'])).
% 1.03/1.23  thf('210', plain,
% 1.03/1.23      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['207', '208', '209'])).
% 1.03/1.23  thf('211', plain,
% 1.03/1.23      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.03/1.23        | ((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 1.03/1.23      inference('demod', [status(thm)], ['175', '180', '183', '210'])).
% 1.03/1.23  thf('212', plain,
% 1.03/1.23      (![X5 : $i]:
% 1.03/1.23         (~ (v1_xboole_0 @ (k1_relat_1 @ X5))
% 1.03/1.23          | ~ (v1_relat_1 @ X5)
% 1.03/1.23          | (v1_xboole_0 @ X5))),
% 1.03/1.23      inference('cnf', [status(esa)], [fc8_relat_1])).
% 1.03/1.23  thf('213', plain,
% 1.03/1.23      ((((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B))
% 1.03/1.23        | (v1_xboole_0 @ sk_C)
% 1.03/1.23        | ~ (v1_relat_1 @ sk_C))),
% 1.03/1.23      inference('sup-', [status(thm)], ['211', '212'])).
% 1.03/1.23  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.23      inference('demod', [status(thm)], ['47', '48'])).
% 1.03/1.23  thf('215', plain,
% 1.03/1.23      ((((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 1.03/1.23      inference('demod', [status(thm)], ['213', '214'])).
% 1.03/1.23  thf('216', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.03/1.23      inference('sup-', [status(thm)], ['114', '115'])).
% 1.03/1.23  thf('217', plain, (((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B))),
% 1.03/1.23      inference('clc', [status(thm)], ['215', '216'])).
% 1.03/1.23  thf('218', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('219', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('220', plain,
% 1.03/1.23      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          != (k2_struct_0 @ sk_B))
% 1.03/1.23        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23            != (k2_struct_0 @ sk_A)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('221', plain,
% 1.03/1.23      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          != (k2_struct_0 @ sk_B)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_B))))),
% 1.03/1.23      inference('split', [status(esa)], ['220'])).
% 1.03/1.23  thf('222', plain,
% 1.03/1.23      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23           != (k2_struct_0 @ sk_B))
% 1.03/1.23         | ~ (l1_struct_0 @ sk_B)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_B))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['219', '221'])).
% 1.03/1.23  thf('223', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('224', plain,
% 1.03/1.23      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          != (k2_struct_0 @ sk_B)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['222', '223'])).
% 1.03/1.23  thf('225', plain,
% 1.03/1.23      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.03/1.23           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23           != (k2_struct_0 @ sk_B))
% 1.03/1.23         | ~ (l1_struct_0 @ sk_A)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_B))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['218', '224'])).
% 1.03/1.23  thf('226', plain, ((l1_struct_0 @ sk_A)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('227', plain,
% 1.03/1.23      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          != (k2_struct_0 @ sk_B)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['225', '226'])).
% 1.03/1.23  thf('228', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('229', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('230', plain,
% 1.03/1.23      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          != (k2_relat_1 @ sk_C)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['227', '228', '229'])).
% 1.03/1.23  thf('231', plain,
% 1.03/1.23      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.03/1.23          != (k2_relat_1 @ sk_C)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_B))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['217', '230'])).
% 1.03/1.23  thf('232', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.03/1.23  thf('233', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.03/1.23      inference('clc', [status(thm)], ['28', '38'])).
% 1.03/1.23  thf('234', plain,
% 1.03/1.23      (![X25 : $i, X26 : $i]:
% 1.03/1.23         (~ (v1_partfun1 @ X26 @ X25)
% 1.03/1.23          | ((k1_relat_1 @ X26) = (X25))
% 1.03/1.23          | ~ (v4_relat_1 @ X26 @ X25)
% 1.03/1.23          | ~ (v1_relat_1 @ X26))),
% 1.03/1.23      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.03/1.23  thf('235', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ sk_C)
% 1.03/1.23        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.03/1.23        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['233', '234'])).
% 1.03/1.23  thf('236', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.23      inference('demod', [status(thm)], ['47', '48'])).
% 1.03/1.23  thf('237', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_C @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('238', plain,
% 1.03/1.23      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.03/1.23         ((v4_relat_1 @ X8 @ X9)
% 1.03/1.23          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.03/1.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.03/1.23  thf('239', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.03/1.23      inference('sup-', [status(thm)], ['237', '238'])).
% 1.03/1.23  thf('240', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['235', '236', '239'])).
% 1.03/1.23  thf('241', plain,
% 1.03/1.23      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.03/1.23         = (k2_funct_1 @ sk_C))),
% 1.03/1.23      inference('simplify', [status(thm)], ['169'])).
% 1.03/1.23  thf('242', plain,
% 1.03/1.23      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_B))))),
% 1.03/1.23      inference('demod', [status(thm)], ['231', '232', '240', '241'])).
% 1.03/1.23  thf('243', plain,
% 1.03/1.23      (![X7 : $i]:
% 1.03/1.23         (~ (v2_funct_1 @ X7)
% 1.03/1.23          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 1.03/1.23          | ~ (v1_funct_1 @ X7)
% 1.03/1.23          | ~ (v1_relat_1 @ X7))),
% 1.03/1.23      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.03/1.23  thf('244', plain,
% 1.03/1.23      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.03/1.23        (k1_zfmisc_1 @ 
% 1.03/1.23         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.03/1.23      inference('demod', [status(thm)], ['105', '106', '107'])).
% 1.03/1.23  thf('245', plain,
% 1.03/1.23      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.03/1.23         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.03/1.23          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.03/1.23      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.23  thf('246', plain,
% 1.03/1.23      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['244', '245'])).
% 1.03/1.23  thf('247', plain,
% 1.03/1.23      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.03/1.23         = (k2_funct_1 @ sk_C))),
% 1.03/1.23      inference('simplify', [status(thm)], ['169'])).
% 1.03/1.23  thf('248', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('249', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('250', plain,
% 1.03/1.23      (![X27 : $i]:
% 1.03/1.23         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.03/1.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.23  thf('251', plain,
% 1.03/1.23      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          != (k2_struct_0 @ sk_A)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('split', [status(esa)], ['220'])).
% 1.03/1.23  thf('252', plain,
% 1.03/1.23      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23           != (k2_struct_0 @ sk_A))
% 1.03/1.23         | ~ (l1_struct_0 @ sk_B)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['250', '251'])).
% 1.03/1.23  thf('253', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('254', plain,
% 1.03/1.23      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          != (k2_struct_0 @ sk_A)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('demod', [status(thm)], ['252', '253'])).
% 1.03/1.23  thf('255', plain,
% 1.03/1.23      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23           != (k2_struct_0 @ sk_A))
% 1.03/1.23         | ~ (l1_struct_0 @ sk_B)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['249', '254'])).
% 1.03/1.23  thf('256', plain, ((l1_struct_0 @ sk_B)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('257', plain,
% 1.03/1.23      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          != (k2_struct_0 @ sk_A)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('demod', [status(thm)], ['255', '256'])).
% 1.03/1.23  thf('258', plain,
% 1.03/1.23      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.03/1.23          != (k2_struct_0 @ sk_A)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['248', '257'])).
% 1.03/1.23  thf('259', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.03/1.23      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.23  thf('260', plain,
% 1.03/1.23      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.03/1.23          != (k2_struct_0 @ sk_A)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('demod', [status(thm)], ['258', '259'])).
% 1.03/1.23  thf('261', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['235', '236', '239'])).
% 1.03/1.23  thf('262', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['235', '236', '239'])).
% 1.03/1.23  thf('263', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.03/1.23      inference('demod', [status(thm)], ['44', '49', '52'])).
% 1.03/1.23  thf('264', plain,
% 1.03/1.23      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.03/1.23          != (k1_relat_1 @ sk_C)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('demod', [status(thm)], ['260', '261', '262', '263'])).
% 1.03/1.23  thf('265', plain,
% 1.03/1.23      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['247', '264'])).
% 1.03/1.23  thf('266', plain,
% 1.03/1.23      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['246', '265'])).
% 1.03/1.23  thf('267', plain,
% 1.03/1.23      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.03/1.23         | ~ (v1_relat_1 @ sk_C)
% 1.03/1.23         | ~ (v1_funct_1 @ sk_C)
% 1.03/1.23         | ~ (v2_funct_1 @ sk_C)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['243', '266'])).
% 1.03/1.23  thf('268', plain, ((v1_relat_1 @ sk_C)),
% 1.03/1.23      inference('demod', [status(thm)], ['47', '48'])).
% 1.03/1.23  thf('269', plain, ((v1_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('270', plain, ((v2_funct_1 @ sk_C)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('271', plain,
% 1.03/1.23      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.03/1.23         <= (~
% 1.03/1.23             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23                = (k2_struct_0 @ sk_A))))),
% 1.03/1.23      inference('demod', [status(thm)], ['267', '268', '269', '270'])).
% 1.03/1.23  thf('272', plain,
% 1.03/1.23      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          = (k2_struct_0 @ sk_A)))),
% 1.03/1.23      inference('simplify', [status(thm)], ['271'])).
% 1.03/1.23  thf('273', plain,
% 1.03/1.23      (~
% 1.03/1.23       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          = (k2_struct_0 @ sk_B))) | 
% 1.03/1.23       ~
% 1.03/1.23       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          = (k2_struct_0 @ sk_A)))),
% 1.03/1.23      inference('split', [status(esa)], ['220'])).
% 1.03/1.23  thf('274', plain,
% 1.03/1.23      (~
% 1.03/1.23       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.03/1.23          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.03/1.23          = (k2_struct_0 @ sk_B)))),
% 1.03/1.23      inference('sat_resolution*', [status(thm)], ['272', '273'])).
% 1.03/1.23  thf('275', plain,
% 1.03/1.23      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.03/1.23         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.03/1.23      inference('simpl_trail', [status(thm)], ['242', '274'])).
% 1.03/1.23  thf('276', plain, ($false),
% 1.03/1.23      inference('simplify_reflect-', [status(thm)], ['118', '275'])).
% 1.03/1.23  
% 1.03/1.23  % SZS output end Refutation
% 1.03/1.23  
% 1.03/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
