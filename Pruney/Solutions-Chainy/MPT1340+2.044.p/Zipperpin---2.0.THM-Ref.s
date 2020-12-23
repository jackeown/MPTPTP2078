%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wnNg4BUMY0

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:13 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  406 (6019 expanded)
%              Number of leaves         :   56 (1817 expanded)
%              Depth                    :   33
%              Number of atoms          : 3675 (119255 expanded)
%              Number of equality atoms :  193 (3474 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
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

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X44 @ X43 @ X42 )
       != X43 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','14','19','20'])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X44 @ X43 @ X42 )
       != X43 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('36',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('40',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','42','47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('57',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('58',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('61',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('62',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('63',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['60','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','80','81','82'])).

thf('84',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['55','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('88',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91'])).

thf('93',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','54','92'])).

thf('94',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','95'])).

thf('97',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('100',plain,(
    ! [X51: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

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

thf('107',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('108',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

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

thf('115',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
        = ( k2_funct_1 @ X25 ) )
      | ( ( k5_relat_1 @ X24 @ X25 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X25 ) )
      | ~ ( v2_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('116',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('117',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
        = ( k2_funct_1 @ X25 ) )
      | ( ( k5_relat_1 @ X24 @ X25 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X25 ) )
      | ~ ( v2_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
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
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('120',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('121',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('122',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('124',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('125',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('126',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X20 ) @ ( k9_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['123','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','134'])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['119','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('141',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('146',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_partfun1 @ X36 @ X35 )
      | ( ( k1_relat_1 @ X36 )
        = X35 )
      | ~ ( v4_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('147',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('150',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('151',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148','151'])).

thf('153',plain,(
    ! [X51: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('154',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','158'])).

thf('160',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('161',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('162',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X44 @ X43 @ X42 )
       != X43 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('163',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('166',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('167',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('171',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91'])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('174',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) )
     != ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['118','159','160','169','170','171','172','173'])).

thf('175',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

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

thf('177',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X21 )
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('178',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('179',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('180',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('181',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('183',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['168'])).

thf('184',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('185',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('188',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['178','181','182','183','184','185','186','187'])).

thf('189',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['175','189'])).

thf('191',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('192',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('193',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('194',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('195',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('196',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['194','199'])).

thf('201',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['193','202'])).

thf('204',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X49: $i] :
      ( ( ( k2_struct_0 @ X49 )
        = ( u1_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('207',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('209',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('211',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('213',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('215',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['206','215'])).

thf('217',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('220',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('221',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('222',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('223',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['205','222'])).

thf('224',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

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

thf('225',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k2_relset_1 @ X53 @ X52 @ X54 )
       != X52 )
      | ~ ( v2_funct_1 @ X54 )
      | ( ( k2_tops_2 @ X53 @ X52 @ X54 )
        = ( k2_funct_1 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X52 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('226',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('229',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('231',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['226','227','228','229','230'])).

thf('232',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['223','232'])).

thf('234',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['192','233'])).

thf('235',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['191','236'])).

thf('238',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['237','238'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('240',plain,(
    ! [X18: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('241',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('242',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k2_relset_1 @ X53 @ X52 @ X54 )
       != X52 )
      | ~ ( v2_funct_1 @ X54 )
      | ( ( k2_tops_2 @ X53 @ X52 @ X54 )
        = ( k2_funct_1 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X52 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('243',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['168'])).

thf('245',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('246',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('247',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('248',plain,(
    ! [X48: $i] :
      ( ( v1_funct_2 @ X48 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('249',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91'])).

thf('251',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['246','251'])).

thf('253',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('254',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['245','255'])).

thf('257',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['256','257','258'])).

thf('260',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('261',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('263',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('264',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('265',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('266',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('267',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['264','267'])).

thf('269',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91'])).

thf('270',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('271',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['268','269','270'])).

thf('272',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['263','271'])).

thf('273',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('274',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['272','273','274'])).

thf('276',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['262','275'])).

thf('277',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('278',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('281',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('282',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('283',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['243','244','261','282'])).

thf('284',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['240','284'])).

thf('286',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('287',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['285','286','287','288'])).

thf('290',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['239','289'])).

thf('291',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['190','290'])).

thf('292',plain,(
    ! [X18: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('293',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('294',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X44 @ X43 @ X42 )
       != X43 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('295',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['168'])).

thf('297',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('298',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('299',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['295','296','297','298'])).

thf('300',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['292','300'])).

thf('302',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('303',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['301','302','303','304'])).

thf('306',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('307',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r2_funct_2 @ X38 @ X39 @ X40 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('308',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['306','307'])).

thf('309',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('311',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['308','309','310'])).

thf('312',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('313',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('314',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('315',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['311','312','313','314'])).

thf('316',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['305','315'])).

thf('317',plain,(
    ! [X18: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('318',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('319',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X44 @ X43 @ X42 )
       != X43 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('320',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['168'])).

thf('322',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('323',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('324',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['320','321','322','323'])).

thf('325',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['324'])).

thf('326',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['317','325'])).

thf('327',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('328',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['326','327','328','329'])).

thf('331',plain,(
    ! [X18: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('332',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('333',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X44 @ X43 @ X42 )
       != X43 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X42 ) @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('334',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['332','333'])).

thf('335',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['168'])).

thf('336',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['259','260'])).

thf('337',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('338',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['334','335','336','337'])).

thf('339',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['338'])).

thf('340',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['331','339'])).

thf('341',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('342',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['340','341','342','343'])).

thf('345',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['316','330','344'])).

thf('346',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['291','345'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('347',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('348',plain,(
    $false ),
    inference(demod,[status(thm)],['105','346','347'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wnNg4BUMY0
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 1065 iterations in 0.478s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/0.94  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.75/0.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.94  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.75/0.94  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.75/0.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.94  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.75/0.94  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.75/0.94  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.75/0.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.94  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.75/0.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.94  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.75/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.94  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.75/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.94  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.75/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.75/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.94  thf(d3_struct_0, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.75/0.94  thf('0', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('1', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('2', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf(t64_tops_2, conjecture,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( l1_struct_0 @ A ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.75/0.94           ( ![C:$i]:
% 0.75/0.94             ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.94                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/0.94                 ( m1_subset_1 @
% 0.75/0.94                   C @ 
% 0.75/0.94                   ( k1_zfmisc_1 @
% 0.75/0.94                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/0.94               ( ( ( ( k2_relset_1 @
% 0.75/0.94                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.75/0.94                     ( k2_struct_0 @ B ) ) & 
% 0.75/0.94                   ( v2_funct_1 @ C ) ) =>
% 0.75/0.94                 ( r2_funct_2 @
% 0.75/0.94                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.75/0.94                   ( k2_tops_2 @
% 0.75/0.94                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.94                     ( k2_tops_2 @
% 0.75/0.94                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.75/0.94                   C ) ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.94    (~( ![A:$i]:
% 0.75/0.94        ( ( l1_struct_0 @ A ) =>
% 0.75/0.94          ( ![B:$i]:
% 0.75/0.94            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.75/0.94              ( ![C:$i]:
% 0.75/0.94                ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.94                    ( v1_funct_2 @
% 0.75/0.94                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/0.94                    ( m1_subset_1 @
% 0.75/0.94                      C @ 
% 0.75/0.94                      ( k1_zfmisc_1 @
% 0.75/0.94                        ( k2_zfmisc_1 @
% 0.75/0.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/0.94                  ( ( ( ( k2_relset_1 @
% 0.75/0.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.75/0.94                        ( k2_struct_0 @ B ) ) & 
% 0.75/0.94                      ( v2_funct_1 @ C ) ) =>
% 0.75/0.94                    ( r2_funct_2 @
% 0.75/0.94                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.75/0.94                      ( k2_tops_2 @
% 0.75/0.94                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.94                        ( k2_tops_2 @
% 0.75/0.94                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.75/0.94                      C ) ) ) ) ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('4', plain,
% 0.75/0.94      (((m1_subset_1 @ sk_C @ 
% 0.75/0.94         (k1_zfmisc_1 @ 
% 0.75/0.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.75/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup+', [status(thm)], ['2', '3'])).
% 0.75/0.94  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('6', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.94  thf(t31_funct_2, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.94       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.75/0.94         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.75/0.94           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.75/0.94           ( m1_subset_1 @
% 0.75/0.94             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.75/0.94         (~ (v2_funct_1 @ X42)
% 0.75/0.94          | ((k2_relset_1 @ X44 @ X43 @ X42) != (X43))
% 0.75/0.94          | (m1_subset_1 @ (k2_funct_1 @ X42) @ 
% 0.75/0.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.75/0.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.75/0.94          | ~ (v1_funct_2 @ X42 @ X44 @ X43)
% 0.75/0.94          | ~ (v1_funct_1 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.94  thf('8', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.94        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94           (k1_zfmisc_1 @ 
% 0.75/0.94            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94            != (u1_struct_0 @ sk_B))
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['6', '7'])).
% 0.75/0.94  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('10', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('12', plain,
% 0.75/0.94      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('14', plain,
% 0.75/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['12', '13'])).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('16', plain,
% 0.75/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('17', plain,
% 0.75/0.94      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94          = (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup+', [status(thm)], ['15', '16'])).
% 0.75/0.94  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['17', '18'])).
% 0.75/0.94  thf('20', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94         (k1_zfmisc_1 @ 
% 0.75/0.94          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.75/0.94      inference('demod', [status(thm)], ['8', '9', '14', '19', '20'])).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B)
% 0.75/0.94        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94           (k1_zfmisc_1 @ 
% 0.75/0.94            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['1', '21'])).
% 0.75/0.94  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('24', plain,
% 0.75/0.94      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.75/0.94        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94           (k1_zfmisc_1 @ 
% 0.75/0.94            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.75/0.94      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/0.94  thf('25', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['24'])).
% 0.75/0.94  thf(cc2_relset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.75/0.94  thf('26', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.94         ((v4_relat_1 @ X26 @ X27)
% 0.75/0.94          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.94  thf('27', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.94  thf(d18_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ B ) =>
% 0.75/0.94       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X9 : $i, X10 : $i]:
% 0.75/0.94         (~ (v4_relat_1 @ X9 @ X10)
% 0.75/0.94          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.75/0.94          | ~ (v1_relat_1 @ X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.75/0.94  thf('29', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94           (u1_struct_0 @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['27', '28'])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (((m1_subset_1 @ sk_C @ 
% 0.75/0.94         (k1_zfmisc_1 @ 
% 0.75/0.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.75/0.94         (~ (v2_funct_1 @ X42)
% 0.75/0.94          | ((k2_relset_1 @ X44 @ X43 @ X42) != (X43))
% 0.75/0.94          | (m1_subset_1 @ (k2_funct_1 @ X42) @ 
% 0.75/0.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.75/0.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.75/0.94          | ~ (v1_funct_2 @ X42 @ X44 @ X43)
% 0.75/0.94          | ~ (v1_funct_1 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94           (k1_zfmisc_1 @ 
% 0.75/0.94            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94            != (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['34', '35'])).
% 0.75/0.94  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['12', '13'])).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['38', '39'])).
% 0.75/0.94  thf('41', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['40', '41'])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['17', '18'])).
% 0.75/0.94  thf('45', plain,
% 0.75/0.94      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94          = (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['43', '44'])).
% 0.75/0.94  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['45', '46'])).
% 0.75/0.94  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94         (k1_zfmisc_1 @ 
% 0.75/0.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.75/0.94      inference('demod', [status(thm)], ['36', '37', '42', '47', '48'])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.75/0.94  thf(cc2_relat_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ A ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.75/0.94  thf('51', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.75/0.94          | (v1_relat_1 @ X7)
% 0.75/0.94          | ~ (v1_relat_1 @ X8))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.75/0.94  thf('52', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ 
% 0.75/0.94           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 0.75/0.94        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/0.94  thf(fc6_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.75/0.94  thf('54', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('demod', [status(thm)], ['52', '53'])).
% 0.75/0.94  thf(t55_funct_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.94       ( ( v2_funct_1 @ A ) =>
% 0.75/0.94         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.75/0.94           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.75/0.94  thf('55', plain,
% 0.75/0.94      (![X23 : $i]:
% 0.75/0.94         (~ (v2_funct_1 @ X23)
% 0.75/0.94          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 0.75/0.94          | ~ (v1_funct_1 @ X23)
% 0.75/0.94          | ~ (v1_relat_1 @ X23))),
% 0.75/0.94      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.75/0.94  thf('56', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(redefinition_k2_relset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.94         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.75/0.94          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.94  thf('58', plain,
% 0.75/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_relat_1 @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.94  thf('59', plain,
% 0.75/0.94      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('60', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf(dt_k2_funct_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.94       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.75/0.94         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.75/0.94  thf('61', plain,
% 0.75/0.94      (![X15 : $i]:
% 0.75/0.94         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (v1_relat_1 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.75/0.94  thf('62', plain,
% 0.75/0.94      (![X15 : $i]:
% 0.75/0.94         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (v1_relat_1 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.75/0.94  thf('63', plain,
% 0.75/0.94      (![X23 : $i]:
% 0.75/0.94         (~ (v2_funct_1 @ X23)
% 0.75/0.94          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 0.75/0.94          | ~ (v1_funct_1 @ X23)
% 0.75/0.94          | ~ (v1_relat_1 @ X23))),
% 0.75/0.94      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.75/0.94  thf(d10_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.94  thf('64', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('65', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.75/0.94      inference('simplify', [status(thm)], ['64'])).
% 0.75/0.94  thf('66', plain,
% 0.75/0.94      (![X9 : $i, X10 : $i]:
% 0.75/0.94         (~ (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.75/0.94          | (v4_relat_1 @ X9 @ X10)
% 0.75/0.94          | ~ (v1_relat_1 @ X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.75/0.94  thf('67', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/0.94  thf('68', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v2_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['63', '67'])).
% 0.75/0.94  thf('69', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v2_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0)
% 0.75/0.94          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['62', '68'])).
% 0.75/0.94  thf('70', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.75/0.94          | ~ (v2_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['69'])).
% 0.75/0.94  thf('71', plain,
% 0.75/0.94      (![X9 : $i, X10 : $i]:
% 0.75/0.94         (~ (v4_relat_1 @ X9 @ X10)
% 0.75/0.94          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.75/0.94          | ~ (v1_relat_1 @ X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.75/0.94  thf('72', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v2_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.75/0.94          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['70', '71'])).
% 0.75/0.94  thf('73', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.75/0.94          | ~ (v2_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['61', '72'])).
% 0.75/0.94  thf('74', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v2_funct_1 @ X0)
% 0.75/0.94          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['73'])).
% 0.75/0.94  thf('75', plain,
% 0.75/0.94      (((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.94      inference('sup+', [status(thm)], ['60', '74'])).
% 0.75/0.94  thf('76', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('77', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.75/0.94          | (v1_relat_1 @ X7)
% 0.75/0.94          | ~ (v1_relat_1 @ X8))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.75/0.94  thf('78', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ 
% 0.75/0.94           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.75/0.94        | (v1_relat_1 @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['76', '77'])).
% 0.75/0.94  thf('79', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.75/0.94  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('83', plain,
% 0.75/0.94      ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['75', '80', '81', '82'])).
% 0.75/0.94  thf('84', plain,
% 0.75/0.94      (![X0 : $i, X2 : $i]:
% 0.75/0.94         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('85', plain,
% 0.75/0.94      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['83', '84'])).
% 0.75/0.94  thf('86', plain,
% 0.75/0.94      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_relat_1 @ sk_C))
% 0.75/0.94        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['55', '85'])).
% 0.75/0.94  thf('87', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('88', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.75/0.94      inference('simplify', [status(thm)], ['64'])).
% 0.75/0.94  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('92', plain,
% 0.75/0.94      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['86', '87', '88', '89', '90', '91'])).
% 0.75/0.94  thf('93', plain, ((r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['29', '54', '92'])).
% 0.75/0.94  thf('94', plain,
% 0.75/0.94      (![X0 : $i, X2 : $i]:
% 0.75/0.94         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('95', plain,
% 0.75/0.94      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | ((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['93', '94'])).
% 0.75/0.94  thf('96', plain,
% 0.75/0.94      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B)
% 0.75/0.94        | ((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['0', '95'])).
% 0.75/0.94  thf('97', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.75/0.94      inference('simplify', [status(thm)], ['64'])).
% 0.75/0.94  thf('98', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('99', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.75/0.94  thf(fc2_struct_0, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.75/0.94       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.75/0.94  thf('100', plain,
% 0.75/0.94      (![X51 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ (u1_struct_0 @ X51))
% 0.75/0.94          | ~ (l1_struct_0 @ X51)
% 0.75/0.94          | (v2_struct_0 @ X51))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.75/0.94  thf('101', plain,
% 0.75/0.94      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | (v2_struct_0 @ sk_B)
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['99', '100'])).
% 0.75/0.94  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('103', plain,
% 0.75/0.94      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['101', '102'])).
% 0.75/0.94  thf('104', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('105', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('clc', [status(thm)], ['103', '104'])).
% 0.75/0.94  thf('106', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.94  thf(t35_funct_2, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.94       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.75/0.94         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.94           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.75/0.94             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.75/0.94  thf('107', plain,
% 0.75/0.94      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.75/0.94         (((X45) = (k1_xboole_0))
% 0.75/0.94          | ~ (v1_funct_1 @ X46)
% 0.75/0.94          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.75/0.94          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.75/0.94          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 0.75/0.94          | ~ (v2_funct_1 @ X46)
% 0.75/0.94          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.75/0.94  thf('108', plain,
% 0.75/0.94      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94          != (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.94        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.75/0.94            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 0.75/0.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['106', '107'])).
% 0.75/0.94  thf('109', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['45', '46'])).
% 0.75/0.94  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('111', plain,
% 0.75/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['40', '41'])).
% 0.75/0.94  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('113', plain,
% 0.75/0.94      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.75/0.94        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.75/0.94            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.75/0.94  thf('114', plain,
% 0.75/0.94      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.75/0.94        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.75/0.94            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['113'])).
% 0.75/0.94  thf(t64_funct_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.75/0.94           ( ( ( v2_funct_1 @ A ) & 
% 0.75/0.94               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.75/0.94               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.75/0.94             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.75/0.94  thf('115', plain,
% 0.75/0.94      (![X24 : $i, X25 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X24)
% 0.75/0.94          | ~ (v1_funct_1 @ X24)
% 0.75/0.94          | ((X24) = (k2_funct_1 @ X25))
% 0.75/0.94          | ((k5_relat_1 @ X24 @ X25) != (k6_relat_1 @ (k2_relat_1 @ X25)))
% 0.75/0.94          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X25))
% 0.75/0.94          | ~ (v2_funct_1 @ X25)
% 0.75/0.94          | ~ (v1_funct_1 @ X25)
% 0.75/0.94          | ~ (v1_relat_1 @ X25))),
% 0.75/0.94      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.75/0.94  thf(redefinition_k6_partfun1, axiom,
% 0.75/0.94    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.75/0.94  thf('116', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.94  thf('117', plain,
% 0.75/0.94      (![X24 : $i, X25 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X24)
% 0.75/0.94          | ~ (v1_funct_1 @ X24)
% 0.75/0.94          | ((X24) = (k2_funct_1 @ X25))
% 0.75/0.94          | ((k5_relat_1 @ X24 @ X25) != (k6_partfun1 @ (k2_relat_1 @ X25)))
% 0.75/0.94          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X25))
% 0.75/0.94          | ~ (v2_funct_1 @ X25)
% 0.75/0.94          | ~ (v1_funct_1 @ X25)
% 0.75/0.94          | ~ (v1_relat_1 @ X25))),
% 0.75/0.94      inference('demod', [status(thm)], ['115', '116'])).
% 0.75/0.94  thf('118', plain,
% 0.75/0.94      ((((k6_partfun1 @ (k2_struct_0 @ sk_A))
% 0.75/0.94          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.75/0.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_relat_1 @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['114', '117'])).
% 0.75/0.94  thf('119', plain,
% 0.75/0.94      (![X15 : $i]:
% 0.75/0.94         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (v1_relat_1 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.75/0.94  thf('120', plain,
% 0.75/0.94      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['86', '87', '88', '89', '90', '91'])).
% 0.75/0.94  thf(t146_relat_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ A ) =>
% 0.75/0.94       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.75/0.94  thf('121', plain,
% 0.75/0.94      (![X13 : $i]:
% 0.75/0.94         (((k9_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (k2_relat_1 @ X13))
% 0.75/0.94          | ~ (v1_relat_1 @ X13))),
% 0.75/0.94      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.75/0.94  thf('122', plain,
% 0.75/0.94      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.75/0.94          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['120', '121'])).
% 0.75/0.94  thf('123', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('124', plain,
% 0.75/0.94      (![X13 : $i]:
% 0.75/0.94         (((k9_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (k2_relat_1 @ X13))
% 0.75/0.94          | ~ (v1_relat_1 @ X13))),
% 0.75/0.94      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.75/0.94  thf('125', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.75/0.94      inference('simplify', [status(thm)], ['64'])).
% 0.75/0.94  thf(t177_funct_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.75/0.94           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.75/0.94             ( B ) ) ) ) ))).
% 0.75/0.94  thf('126', plain,
% 0.75/0.94      (![X19 : $i, X20 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.75/0.94          | ((k9_relat_1 @ (k2_funct_1 @ X20) @ (k9_relat_1 @ X20 @ X19))
% 0.75/0.94              = (X19))
% 0.75/0.94          | ~ (v2_funct_1 @ X20)
% 0.75/0.94          | ~ (v1_funct_1 @ X20)
% 0.75/0.94          | ~ (v1_relat_1 @ X20))),
% 0.75/0.94      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.75/0.94  thf('127', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v2_funct_1 @ X0)
% 0.75/0.94          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.75/0.94              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['125', '126'])).
% 0.75/0.94  thf('128', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.75/0.94            = (k1_relat_1 @ X0))
% 0.75/0.94          | ~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v2_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['124', '127'])).
% 0.75/0.94  thf('129', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v2_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ X0)
% 0.75/0.94          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.75/0.94              = (k1_relat_1 @ X0)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['128'])).
% 0.75/0.94  thf('130', plain,
% 0.75/0.94      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.75/0.94          = (k1_relat_1 @ sk_C))
% 0.75/0.94        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C))),
% 0.75/0.94      inference('sup+', [status(thm)], ['123', '129'])).
% 0.75/0.94  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('134', plain,
% 0.75/0.94      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.75/0.94         = (k1_relat_1 @ sk_C))),
% 0.75/0.94      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.75/0.94  thf('135', plain,
% 0.75/0.94      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['122', '134'])).
% 0.75/0.94  thf('136', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['119', '135'])).
% 0.75/0.94  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('139', plain,
% 0.75/0.94      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.75/0.94  thf('140', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.94  thf(cc5_funct_2, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.75/0.94       ( ![C:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.75/0.94             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.75/0.94  thf('141', plain,
% 0.75/0.94      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.75/0.94          | (v1_partfun1 @ X32 @ X33)
% 0.75/0.94          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.75/0.94          | ~ (v1_funct_1 @ X32)
% 0.75/0.94          | (v1_xboole_0 @ X34))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.75/0.94  thf('142', plain,
% 0.75/0.94      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.94        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['140', '141'])).
% 0.75/0.94  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('144', plain,
% 0.75/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['12', '13'])).
% 0.75/0.94  thf('145', plain,
% 0.75/0.94      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.94        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.75/0.94  thf(d4_partfun1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.75/0.94       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.75/0.94  thf('146', plain,
% 0.75/0.94      (![X35 : $i, X36 : $i]:
% 0.75/0.94         (~ (v1_partfun1 @ X36 @ X35)
% 0.75/0.94          | ((k1_relat_1 @ X36) = (X35))
% 0.75/0.94          | ~ (v4_relat_1 @ X36 @ X35)
% 0.75/0.94          | ~ (v1_relat_1 @ X36))),
% 0.75/0.94      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.75/0.94  thf('147', plain,
% 0.75/0.94      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.94        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.75/0.94        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['145', '146'])).
% 0.75/0.94  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('149', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.94  thf('150', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.94         ((v4_relat_1 @ X26 @ X27)
% 0.75/0.94          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.94  thf('151', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['149', '150'])).
% 0.75/0.94  thf('152', plain,
% 0.75/0.94      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.94        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['147', '148', '151'])).
% 0.75/0.94  thf('153', plain,
% 0.75/0.94      (![X51 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ (u1_struct_0 @ X51))
% 0.75/0.94          | ~ (l1_struct_0 @ X51)
% 0.75/0.94          | (v2_struct_0 @ X51))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.75/0.94  thf('154', plain,
% 0.75/0.94      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.75/0.94        | (v2_struct_0 @ sk_B)
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['152', '153'])).
% 0.75/0.94  thf('155', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('156', plain,
% 0.75/0.94      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['154', '155'])).
% 0.75/0.94  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('158', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('clc', [status(thm)], ['156', '157'])).
% 0.75/0.94  thf('159', plain,
% 0.75/0.94      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['139', '158'])).
% 0.75/0.94  thf('160', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('demod', [status(thm)], ['52', '53'])).
% 0.75/0.94  thf('161', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.94  thf('162', plain,
% 0.75/0.94      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.75/0.94         (~ (v2_funct_1 @ X42)
% 0.75/0.94          | ((k2_relset_1 @ X44 @ X43 @ X42) != (X43))
% 0.75/0.94          | (v1_funct_1 @ (k2_funct_1 @ X42))
% 0.75/0.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.75/0.94          | ~ (v1_funct_2 @ X42 @ X44 @ X43)
% 0.75/0.94          | ~ (v1_funct_1 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.94  thf('163', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94            != (k2_struct_0 @ sk_B))
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['161', '162'])).
% 0.75/0.94  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('165', plain,
% 0.75/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['40', '41'])).
% 0.75/0.94  thf('166', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['45', '46'])).
% 0.75/0.94  thf('167', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('168', plain,
% 0.75/0.94      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.75/0.94      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 0.75/0.94  thf('169', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('simplify', [status(thm)], ['168'])).
% 0.75/0.94  thf('170', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('171', plain,
% 0.75/0.94      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['86', '87', '88', '89', '90', '91'])).
% 0.75/0.94  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('174', plain,
% 0.75/0.94      ((((k6_partfun1 @ (k2_struct_0 @ sk_A))
% 0.75/0.94          != (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.75/0.94        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.94      inference('demod', [status(thm)],
% 0.75/0.94                ['118', '159', '160', '169', '170', '171', '172', '173'])).
% 0.75/0.94  thf('175', plain,
% 0.75/0.94      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['174'])).
% 0.75/0.94  thf('176', plain,
% 0.75/0.94      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.75/0.94        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.75/0.94            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['113'])).
% 0.75/0.94  thf(t48_funct_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.75/0.94           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.75/0.94               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.75/0.94             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.75/0.94  thf('177', plain,
% 0.75/0.94      (![X21 : $i, X22 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X21)
% 0.75/0.94          | ~ (v1_funct_1 @ X21)
% 0.75/0.94          | (v2_funct_1 @ X22)
% 0.75/0.94          | ((k2_relat_1 @ X21) != (k1_relat_1 @ X22))
% 0.75/0.94          | ~ (v2_funct_1 @ (k5_relat_1 @ X21 @ X22))
% 0.75/0.94          | ~ (v1_funct_1 @ X22)
% 0.75/0.94          | ~ (v1_relat_1 @ X22))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.75/0.94  thf('178', plain,
% 0.75/0.94      ((~ (v2_funct_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.75/0.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_relat_1 @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['176', '177'])).
% 0.75/0.94  thf(fc4_funct_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.75/0.94       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.75/0.94  thf('179', plain, (![X17 : $i]: (v2_funct_1 @ (k6_relat_1 @ X17))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.75/0.94  thf('180', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.94  thf('181', plain, (![X17 : $i]: (v2_funct_1 @ (k6_partfun1 @ X17))),
% 0.75/0.94      inference('demod', [status(thm)], ['179', '180'])).
% 0.75/0.94  thf('182', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('demod', [status(thm)], ['52', '53'])).
% 0.75/0.94  thf('183', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('simplify', [status(thm)], ['168'])).
% 0.75/0.94  thf('184', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('185', plain,
% 0.75/0.94      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['86', '87', '88', '89', '90', '91'])).
% 0.75/0.94  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('188', plain,
% 0.75/0.94      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.75/0.94        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)],
% 0.75/0.94                ['178', '181', '182', '183', '184', '185', '186', '187'])).
% 0.75/0.94  thf('189', plain,
% 0.75/0.94      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['188'])).
% 0.75/0.94  thf('190', plain,
% 0.75/0.94      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.75/0.94        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.94      inference('clc', [status(thm)], ['175', '189'])).
% 0.75/0.94  thf('191', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('192', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('193', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('194', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('195', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('196', plain,
% 0.75/0.94      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.94          sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('197', plain,
% 0.75/0.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.94           sk_C)
% 0.75/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['195', '196'])).
% 0.75/0.94  thf('198', plain, ((l1_struct_0 @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('199', plain,
% 0.75/0.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.94          sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['197', '198'])).
% 0.75/0.94  thf('200', plain,
% 0.75/0.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.94           sk_C)
% 0.75/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['194', '199'])).
% 0.75/0.94  thf('201', plain, ((l1_struct_0 @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('202', plain,
% 0.75/0.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.94          sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['200', '201'])).
% 0.75/0.94  thf('203', plain,
% 0.75/0.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.94           sk_C)
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['193', '202'])).
% 0.75/0.94  thf('204', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('205', plain,
% 0.75/0.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.94          sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['203', '204'])).
% 0.75/0.94  thf('206', plain,
% 0.75/0.94      (![X49 : $i]:
% 0.75/0.94         (((k2_struct_0 @ X49) = (u1_struct_0 @ X49)) | ~ (l1_struct_0 @ X49))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.75/0.94  thf('207', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('208', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.94         ((v4_relat_1 @ X26 @ X27)
% 0.75/0.94          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.94  thf('209', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['207', '208'])).
% 0.75/0.94  thf('210', plain,
% 0.75/0.94      (![X9 : $i, X10 : $i]:
% 0.75/0.94         (~ (v4_relat_1 @ X9 @ X10)
% 0.75/0.94          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.75/0.94          | ~ (v1_relat_1 @ X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.75/0.94  thf('211', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['209', '210'])).
% 0.75/0.94  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('213', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['211', '212'])).
% 0.75/0.94  thf('214', plain,
% 0.75/0.94      (![X0 : $i, X2 : $i]:
% 0.75/0.94         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('215', plain,
% 0.75/0.94      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k1_relat_1 @ sk_C))
% 0.75/0.94        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['213', '214'])).
% 0.75/0.94  thf('216', plain,
% 0.75/0.94      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k1_relat_1 @ sk_C))
% 0.75/0.94        | ~ (l1_struct_0 @ sk_A)
% 0.75/0.94        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['206', '215'])).
% 0.75/0.94  thf('217', plain, ((l1_struct_0 @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('218', plain,
% 0.75/0.94      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k1_relat_1 @ sk_C))
% 0.75/0.94        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['216', '217'])).
% 0.75/0.94  thf('219', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('clc', [status(thm)], ['156', '157'])).
% 0.75/0.94  thf('220', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.75/0.94      inference('simplify', [status(thm)], ['64'])).
% 0.75/0.94  thf('221', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('clc', [status(thm)], ['156', '157'])).
% 0.75/0.94  thf('222', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 0.75/0.94  thf('223', plain,
% 0.75/0.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.75/0.94          sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['205', '222'])).
% 0.75/0.94  thf('224', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.94  thf(d4_tops_2, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.94       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.75/0.94         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.75/0.94  thf('225', plain,
% 0.75/0.94      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.75/0.94         (((k2_relset_1 @ X53 @ X52 @ X54) != (X52))
% 0.75/0.94          | ~ (v2_funct_1 @ X54)
% 0.75/0.94          | ((k2_tops_2 @ X53 @ X52 @ X54) = (k2_funct_1 @ X54))
% 0.75/0.94          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 0.75/0.94          | ~ (v1_funct_2 @ X54 @ X53 @ X52)
% 0.75/0.94          | ~ (v1_funct_1 @ X54))),
% 0.75/0.94      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.75/0.94  thf('226', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94            = (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94            != (k2_struct_0 @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['224', '225'])).
% 0.75/0.94  thf('227', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('228', plain,
% 0.75/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['40', '41'])).
% 0.75/0.94  thf('229', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('230', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['45', '46'])).
% 0.75/0.94  thf('231', plain,
% 0.75/0.94      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94          = (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.75/0.94      inference('demod', [status(thm)], ['226', '227', '228', '229', '230'])).
% 0.75/0.94  thf('232', plain,
% 0.75/0.94      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.75/0.94         = (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('simplify', [status(thm)], ['231'])).
% 0.75/0.94  thf('233', plain,
% 0.75/0.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.75/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94           (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94          sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['223', '232'])).
% 0.75/0.94  thf('234', plain,
% 0.75/0.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94           sk_C)
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['192', '233'])).
% 0.75/0.94  thf('235', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('236', plain,
% 0.75/0.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94           (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94          sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['234', '235'])).
% 0.75/0.94  thf('237', plain,
% 0.75/0.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94           sk_C)
% 0.75/0.94        | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['191', '236'])).
% 0.75/0.94  thf('238', plain, ((l1_struct_0 @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('239', plain,
% 0.75/0.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94           (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94          sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['237', '238'])).
% 0.75/0.94  thf(fc6_funct_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.75/0.94       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.75/0.94         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.75/0.94         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.75/0.94  thf('240', plain,
% 0.75/0.94      (![X18 : $i]:
% 0.75/0.94         ((v2_funct_1 @ (k2_funct_1 @ X18))
% 0.75/0.94          | ~ (v2_funct_1 @ X18)
% 0.75/0.94          | ~ (v1_funct_1 @ X18)
% 0.75/0.94          | ~ (v1_relat_1 @ X18))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.94  thf('241', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.75/0.94  thf('242', plain,
% 0.75/0.94      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.75/0.94         (((k2_relset_1 @ X53 @ X52 @ X54) != (X52))
% 0.75/0.94          | ~ (v2_funct_1 @ X54)
% 0.75/0.94          | ((k2_tops_2 @ X53 @ X52 @ X54) = (k2_funct_1 @ X54))
% 0.75/0.94          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 0.75/0.94          | ~ (v1_funct_2 @ X54 @ X53 @ X52)
% 0.75/0.94          | ~ (v1_funct_1 @ X54))),
% 0.75/0.94      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.75/0.94  thf('243', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94             (k2_struct_0 @ sk_A))
% 0.75/0.94        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['241', '242'])).
% 0.75/0.94  thf('244', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('simplify', [status(thm)], ['168'])).
% 0.75/0.94  thf('245', plain,
% 0.75/0.94      (![X15 : $i]:
% 0.75/0.94         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (v1_relat_1 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.75/0.94  thf('246', plain,
% 0.75/0.94      (![X15 : $i]:
% 0.75/0.94         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (v1_relat_1 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.75/0.94  thf('247', plain,
% 0.75/0.94      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.75/0.94  thf(t3_funct_2, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.94       ( ( v1_funct_1 @ A ) & 
% 0.75/0.94         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.75/0.94         ( m1_subset_1 @
% 0.75/0.94           A @ 
% 0.75/0.94           ( k1_zfmisc_1 @
% 0.75/0.94             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.75/0.94  thf('248', plain,
% 0.75/0.94      (![X48 : $i]:
% 0.75/0.94         ((v1_funct_2 @ X48 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))
% 0.75/0.94          | ~ (v1_funct_1 @ X48)
% 0.75/0.94          | ~ (v1_relat_1 @ X48))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.75/0.94  thf('249', plain,
% 0.75/0.94      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))
% 0.75/0.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['247', '248'])).
% 0.75/0.94  thf('250', plain,
% 0.75/0.94      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['86', '87', '88', '89', '90', '91'])).
% 0.75/0.94  thf('251', plain,
% 0.75/0.94      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94         (k1_relat_1 @ sk_C))
% 0.75/0.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['249', '250'])).
% 0.75/0.94  thf('252', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94           (k1_relat_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['246', '251'])).
% 0.75/0.94  thf('253', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('254', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('255', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94           (k1_relat_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['252', '253', '254'])).
% 0.75/0.94  thf('256', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94           (k1_relat_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['245', '255'])).
% 0.75/0.94  thf('257', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('259', plain,
% 0.75/0.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94        (k1_relat_1 @ sk_C))),
% 0.75/0.94      inference('demod', [status(thm)], ['256', '257', '258'])).
% 0.75/0.94  thf('260', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('clc', [status(thm)], ['156', '157'])).
% 0.75/0.94  thf('261', plain,
% 0.75/0.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94        (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['259', '260'])).
% 0.75/0.94  thf('262', plain,
% 0.75/0.94      (![X15 : $i]:
% 0.75/0.94         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (v1_relat_1 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.75/0.94  thf('263', plain,
% 0.75/0.94      (![X15 : $i]:
% 0.75/0.94         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 0.75/0.94          | ~ (v1_funct_1 @ X15)
% 0.75/0.94          | ~ (v1_relat_1 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.75/0.94  thf('264', plain,
% 0.75/0.94      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.75/0.94  thf('265', plain,
% 0.75/0.94      (![X48 : $i]:
% 0.75/0.94         ((m1_subset_1 @ X48 @ 
% 0.75/0.94           (k1_zfmisc_1 @ 
% 0.75/0.94            (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))))
% 0.75/0.94          | ~ (v1_funct_1 @ X48)
% 0.75/0.94          | ~ (v1_relat_1 @ X48))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.75/0.94  thf('266', plain,
% 0.75/0.94      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.94         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.75/0.94          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.94  thf('267', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.75/0.94              = (k2_relat_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['265', '266'])).
% 0.75/0.94  thf('268', plain,
% 0.75/0.94      ((((k2_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94          (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C))
% 0.75/0.94          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['264', '267'])).
% 0.75/0.94  thf('269', plain,
% 0.75/0.94      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['86', '87', '88', '89', '90', '91'])).
% 0.75/0.94  thf('270', plain,
% 0.75/0.94      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.75/0.94  thf('271', plain,
% 0.75/0.94      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.75/0.94          (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['268', '269', '270'])).
% 0.75/0.94  thf('272', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['263', '271'])).
% 0.75/0.94  thf('273', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('274', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('275', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['272', '273', '274'])).
% 0.75/0.94  thf('276', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['262', '275'])).
% 0.75/0.94  thf('277', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('278', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('279', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.75/0.94         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.75/0.94      inference('demod', [status(thm)], ['276', '277', '278'])).
% 0.75/0.94  thf('280', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('clc', [status(thm)], ['156', '157'])).
% 0.75/0.94  thf('281', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('clc', [status(thm)], ['156', '157'])).
% 0.75/0.94  thf('282', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['279', '280', '281'])).
% 0.75/0.94  thf('283', plain,
% 0.75/0.94      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['243', '244', '261', '282'])).
% 0.75/0.94  thf('284', plain,
% 0.75/0.94      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['283'])).
% 0.75/0.94  thf('285', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.94        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['240', '284'])).
% 0.75/0.94  thf('286', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('287', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('288', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('289', plain,
% 0.75/0.94      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['285', '286', '287', '288'])).
% 0.75/0.94  thf('290', plain,
% 0.75/0.94      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['239', '289'])).
% 0.75/0.94  thf('291', plain,
% 0.75/0.94      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.94           sk_C)
% 0.75/0.94        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['190', '290'])).
% 0.75/0.94  thf('292', plain,
% 0.75/0.94      (![X18 : $i]:
% 0.75/0.94         ((v2_funct_1 @ (k2_funct_1 @ X18))
% 0.75/0.94          | ~ (v2_funct_1 @ X18)
% 0.75/0.94          | ~ (v1_funct_1 @ X18)
% 0.75/0.94          | ~ (v1_relat_1 @ X18))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.94  thf('293', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.75/0.94  thf('294', plain,
% 0.75/0.94      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.75/0.94         (~ (v2_funct_1 @ X42)
% 0.75/0.94          | ((k2_relset_1 @ X44 @ X43 @ X42) != (X43))
% 0.75/0.94          | (m1_subset_1 @ (k2_funct_1 @ X42) @ 
% 0.75/0.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.75/0.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.75/0.94          | ~ (v1_funct_2 @ X42 @ X44 @ X43)
% 0.75/0.94          | ~ (v1_funct_1 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.94  thf('295', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94             (k2_struct_0 @ sk_A))
% 0.75/0.94        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94           (k1_zfmisc_1 @ 
% 0.75/0.94            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['293', '294'])).
% 0.75/0.94  thf('296', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('simplify', [status(thm)], ['168'])).
% 0.75/0.94  thf('297', plain,
% 0.75/0.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94        (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['259', '260'])).
% 0.75/0.94  thf('298', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['279', '280', '281'])).
% 0.75/0.94  thf('299', plain,
% 0.75/0.94      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94         (k1_zfmisc_1 @ 
% 0.75/0.94          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.75/0.94        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['295', '296', '297', '298'])).
% 0.75/0.94  thf('300', plain,
% 0.75/0.94      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94           (k1_zfmisc_1 @ 
% 0.75/0.94            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['299'])).
% 0.75/0.94  thf('301', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.94        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94           (k1_zfmisc_1 @ 
% 0.75/0.94            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['292', '300'])).
% 0.75/0.94  thf('302', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('303', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('304', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('305', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['301', '302', '303', '304'])).
% 0.75/0.94  thf('306', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.75/0.94      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.94  thf(reflexivity_r2_funct_2, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.94         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.75/0.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.94       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.75/0.94  thf('307', plain,
% 0.75/0.94      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.75/0.94         ((r2_funct_2 @ X38 @ X39 @ X40 @ X40)
% 0.75/0.94          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.75/0.94          | ~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.75/0.94          | ~ (v1_funct_1 @ X40)
% 0.75/0.94          | ~ (v1_funct_1 @ X41)
% 0.75/0.94          | ~ (v1_funct_2 @ X41 @ X38 @ X39)
% 0.75/0.94          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.75/0.94      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.75/0.94  thf('308', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X0 @ 
% 0.75/0.94             (k1_zfmisc_1 @ 
% 0.75/0.94              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.75/0.94          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.94          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.94             sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['306', '307'])).
% 0.75/0.94  thf('309', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('310', plain,
% 0.75/0.94      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['12', '13'])).
% 0.75/0.94  thf('311', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X0 @ 
% 0.75/0.94             (k1_zfmisc_1 @ 
% 0.75/0.94              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.75/0.94          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.94             sk_C))),
% 0.75/0.94      inference('demod', [status(thm)], ['308', '309', '310'])).
% 0.75/0.94  thf('312', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.75/0.94  thf('313', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.75/0.94  thf('314', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.75/0.94  thf('315', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X0 @ 
% 0.75/0.94             (k1_zfmisc_1 @ 
% 0.75/0.94              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.75/0.94          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.75/0.94          | ~ (v1_funct_1 @ X0)
% 0.75/0.94          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.75/0.94             sk_C))),
% 0.75/0.94      inference('demod', [status(thm)], ['311', '312', '313', '314'])).
% 0.75/0.94  thf('316', plain,
% 0.75/0.94      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94             (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['305', '315'])).
% 0.75/0.94  thf('317', plain,
% 0.75/0.94      (![X18 : $i]:
% 0.75/0.94         ((v2_funct_1 @ (k2_funct_1 @ X18))
% 0.75/0.94          | ~ (v2_funct_1 @ X18)
% 0.75/0.94          | ~ (v1_funct_1 @ X18)
% 0.75/0.94          | ~ (v1_relat_1 @ X18))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.94  thf('318', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.75/0.94  thf('319', plain,
% 0.75/0.94      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.75/0.94         (~ (v2_funct_1 @ X42)
% 0.75/0.94          | ((k2_relset_1 @ X44 @ X43 @ X42) != (X43))
% 0.75/0.94          | (v1_funct_1 @ (k2_funct_1 @ X42))
% 0.75/0.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.75/0.94          | ~ (v1_funct_2 @ X42 @ X44 @ X43)
% 0.75/0.94          | ~ (v1_funct_1 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.94  thf('320', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94             (k2_struct_0 @ sk_A))
% 0.75/0.94        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['318', '319'])).
% 0.75/0.94  thf('321', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('simplify', [status(thm)], ['168'])).
% 0.75/0.94  thf('322', plain,
% 0.75/0.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94        (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['259', '260'])).
% 0.75/0.94  thf('323', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['279', '280', '281'])).
% 0.75/0.94  thf('324', plain,
% 0.75/0.94      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.75/0.94        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['320', '321', '322', '323'])).
% 0.75/0.94  thf('325', plain,
% 0.75/0.94      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['324'])).
% 0.75/0.94  thf('326', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.94        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['317', '325'])).
% 0.75/0.94  thf('327', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('328', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('329', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('330', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['326', '327', '328', '329'])).
% 0.75/0.94  thf('331', plain,
% 0.75/0.94      (![X18 : $i]:
% 0.75/0.94         ((v2_funct_1 @ (k2_funct_1 @ X18))
% 0.75/0.94          | ~ (v2_funct_1 @ X18)
% 0.75/0.94          | ~ (v1_funct_1 @ X18)
% 0.75/0.94          | ~ (v1_relat_1 @ X18))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.75/0.94  thf('332', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.94        (k1_zfmisc_1 @ 
% 0.75/0.94         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.75/0.94  thf('333', plain,
% 0.75/0.94      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.75/0.94         (~ (v2_funct_1 @ X42)
% 0.75/0.94          | ((k2_relset_1 @ X44 @ X43 @ X42) != (X43))
% 0.75/0.94          | (v1_funct_2 @ (k2_funct_1 @ X42) @ X43 @ X44)
% 0.75/0.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.75/0.94          | ~ (v1_funct_2 @ X42 @ X44 @ X43)
% 0.75/0.94          | ~ (v1_funct_1 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.94  thf('334', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94             (k2_struct_0 @ sk_A))
% 0.75/0.94        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94           (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['332', '333'])).
% 0.75/0.94  thf('335', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.94      inference('simplify', [status(thm)], ['168'])).
% 0.75/0.94  thf('336', plain,
% 0.75/0.94      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.75/0.94        (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['259', '260'])).
% 0.75/0.94  thf('337', plain,
% 0.75/0.94      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.75/0.94         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['279', '280', '281'])).
% 0.75/0.94  thf('338', plain,
% 0.75/0.94      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94         (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.75/0.94        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.75/0.94        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['334', '335', '336', '337'])).
% 0.75/0.94  thf('339', plain,
% 0.75/0.94      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.94        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94           (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['338'])).
% 0.75/0.94  thf('340', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.94        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.94        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94           (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['331', '339'])).
% 0.75/0.94  thf('341', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('342', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('343', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('344', plain,
% 0.75/0.94      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.75/0.94        (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['340', '341', '342', '343'])).
% 0.75/0.94  thf('345', plain,
% 0.75/0.94      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.75/0.94      inference('demod', [status(thm)], ['316', '330', '344'])).
% 0.75/0.94  thf('346', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['291', '345'])).
% 0.75/0.94  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.75/0.94  thf('347', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('348', plain, ($false),
% 0.75/0.94      inference('demod', [status(thm)], ['105', '346', '347'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.80/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
