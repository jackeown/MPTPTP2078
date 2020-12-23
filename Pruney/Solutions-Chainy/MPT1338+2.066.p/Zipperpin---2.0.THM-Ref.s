%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lr6iYVbcVg

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:58 EST 2020

% Result     : Theorem 7.69s
% Output     : Refutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  292 (14498 expanded)
%              Number of leaves         :   53 (4402 expanded)
%              Depth                    :   25
%              Number of atoms          : 2508 (318263 expanded)
%              Number of equality atoms :  176 (15290 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
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

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( v1_partfun1 @ X37 @ X38 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X43: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','39'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('41',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_partfun1 @ X41 @ X40 )
      | ( ( k1_relat_1 @ X41 )
        = X40 )
      | ~ ( v4_relat_1 @ X41 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('54',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('58',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('60',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) @ ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('65',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('66',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_funct_1 @ X17 )
        = ( k4_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('73',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k9_relat_1 @ X18 @ X19 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X18 ) @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ X0 )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66','78'])).

thf('80',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('82',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','85'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('87',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

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

thf('89',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k2_relset_1 @ X45 @ X44 @ X46 )
       != X44 )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_tops_2 @ X45 @ X44 @ X46 )
        = ( k2_funct_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['92','97'])).

thf('99',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('102',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('105',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_partfun1 @ X41 @ X40 )
      | ( ( k1_relat_1 @ X41 )
        = X40 )
      | ~ ( v4_relat_1 @ X41 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('111',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('117',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110','117'])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','118'])).

thf('120',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('124',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['122','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('133',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110','117'])).

thf('135',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','91','119','120','121','135'])).

thf('137',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('139',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X25 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('140',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('143',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k3_relset_1 @ X35 @ X36 @ X34 )
        = ( k4_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('144',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['141','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110','117'])).

thf('149',plain,
    ( ( k3_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['140','149'])).

thf('151',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('152',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('154',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k4_relat_1 @ sk_C )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['140','149'])).

thf('156',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('159',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','159'])).

thf('161',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('162',plain,(
    ! [X13: $i] :
      ( ( ( k10_relat_1 @ X13 @ ( k2_relat_1 @ X13 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('166',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('167',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','159'])).

thf('168',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('170',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['169'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('171',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k9_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['168','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('175',plain,(
    ! [X10: $i] :
      ( ( ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('177',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('179',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('183',plain,
    ( ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['173','174','179','180','181','182'])).

thf('184',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k10_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('185',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','159'])).

thf('186',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165','166','167','183','184','185'])).

thf('187',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('188',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['186','191'])).

thf('193',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','159'])).

thf('194',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('195',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['173','174','179','180','181','182'])).

thf('197',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('198',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('200',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('201',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['192','198','199','200'])).

thf('202',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110','117'])).

thf('203',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14','51','52','53','137','201','202'])).

thf('204',plain,
    ( $false
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165','166','167','183','184','185'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('207',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['205','208'])).

thf('210',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('211',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165','166','167','183','184','185'])).

thf('212',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('213',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('214',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('215',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['136'])).

thf('216',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('217',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('218',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('219',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['216','221'])).

thf('223',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('224',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('226',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('227',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['215','227'])).

thf('229',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','228'])).

thf('230',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('231',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['213','232'])).

thf('234',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['233'])).

thf('235',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('236',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['234','235'])).

thf('237',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['204','236'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lr6iYVbcVg
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 7.69/7.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.69/7.92  % Solved by: fo/fo7.sh
% 7.69/7.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.69/7.92  % done 541 iterations in 7.431s
% 7.69/7.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.69/7.92  % SZS output start Refutation
% 7.69/7.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.69/7.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.69/7.92  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 7.69/7.92  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 7.69/7.92  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 7.69/7.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.69/7.92  thf(sk_C_type, type, sk_C: $i).
% 7.69/7.92  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.69/7.92  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 7.69/7.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.69/7.92  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 7.69/7.92  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 7.69/7.92  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 7.69/7.92  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 7.69/7.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.69/7.92  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.69/7.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 7.69/7.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.69/7.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.69/7.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.69/7.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.69/7.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.69/7.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 7.69/7.92  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 7.69/7.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.69/7.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 7.69/7.92  thf(sk_B_type, type, sk_B: $i).
% 7.69/7.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.69/7.92  thf(sk_A_type, type, sk_A: $i).
% 7.69/7.92  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 7.69/7.92  thf(d3_struct_0, axiom,
% 7.69/7.92    (![A:$i]:
% 7.69/7.92     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 7.69/7.92  thf('0', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('1', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf(t62_tops_2, conjecture,
% 7.69/7.92    (![A:$i]:
% 7.69/7.92     ( ( l1_struct_0 @ A ) =>
% 7.69/7.92       ( ![B:$i]:
% 7.69/7.92         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 7.69/7.92           ( ![C:$i]:
% 7.69/7.92             ( ( ( v1_funct_1 @ C ) & 
% 7.69/7.92                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 7.69/7.92                 ( m1_subset_1 @
% 7.69/7.92                   C @ 
% 7.69/7.92                   ( k1_zfmisc_1 @
% 7.69/7.92                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 7.69/7.92               ( ( ( ( k2_relset_1 @
% 7.69/7.92                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 7.69/7.92                     ( k2_struct_0 @ B ) ) & 
% 7.69/7.92                   ( v2_funct_1 @ C ) ) =>
% 7.69/7.92                 ( ( ( k1_relset_1 @
% 7.69/7.92                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 7.69/7.92                       ( k2_tops_2 @
% 7.69/7.92                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 7.69/7.92                     ( k2_struct_0 @ B ) ) & 
% 7.69/7.92                   ( ( k2_relset_1 @
% 7.69/7.92                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 7.69/7.92                       ( k2_tops_2 @
% 7.69/7.92                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 7.69/7.92                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 7.69/7.92  thf(zf_stmt_0, negated_conjecture,
% 7.69/7.92    (~( ![A:$i]:
% 7.69/7.92        ( ( l1_struct_0 @ A ) =>
% 7.69/7.92          ( ![B:$i]:
% 7.69/7.92            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 7.69/7.92              ( ![C:$i]:
% 7.69/7.92                ( ( ( v1_funct_1 @ C ) & 
% 7.69/7.92                    ( v1_funct_2 @
% 7.69/7.92                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 7.69/7.92                    ( m1_subset_1 @
% 7.69/7.92                      C @ 
% 7.69/7.92                      ( k1_zfmisc_1 @
% 7.69/7.92                        ( k2_zfmisc_1 @
% 7.69/7.92                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 7.69/7.92                  ( ( ( ( k2_relset_1 @
% 7.69/7.92                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 7.69/7.92                        ( k2_struct_0 @ B ) ) & 
% 7.69/7.92                      ( v2_funct_1 @ C ) ) =>
% 7.69/7.92                    ( ( ( k1_relset_1 @
% 7.69/7.92                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 7.69/7.92                          ( k2_tops_2 @
% 7.69/7.92                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 7.69/7.92                        ( k2_struct_0 @ B ) ) & 
% 7.69/7.92                      ( ( k2_relset_1 @
% 7.69/7.92                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 7.69/7.92                          ( k2_tops_2 @
% 7.69/7.92                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 7.69/7.92                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 7.69/7.92    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 7.69/7.92  thf('2', plain,
% 7.69/7.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          != (k2_struct_0 @ sk_B))
% 7.69/7.92        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92            != (k2_struct_0 @ sk_A)))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('3', plain,
% 7.69/7.92      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          != (k2_struct_0 @ sk_A)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_A))))),
% 7.69/7.92      inference('split', [status(esa)], ['2'])).
% 7.69/7.92  thf('4', plain,
% 7.69/7.92      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92           != (k2_struct_0 @ sk_A))
% 7.69/7.92         | ~ (l1_struct_0 @ sk_B)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_A))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['1', '3'])).
% 7.69/7.92  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('6', plain,
% 7.69/7.92      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          != (k2_struct_0 @ sk_A)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_A))))),
% 7.69/7.92      inference('demod', [status(thm)], ['4', '5'])).
% 7.69/7.92  thf('7', plain,
% 7.69/7.92      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92           != (k2_struct_0 @ sk_A))
% 7.69/7.92         | ~ (l1_struct_0 @ sk_B)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_A))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['0', '6'])).
% 7.69/7.92  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('9', plain,
% 7.69/7.92      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          != (k2_struct_0 @ sk_A)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_A))))),
% 7.69/7.92      inference('demod', [status(thm)], ['7', '8'])).
% 7.69/7.92  thf('10', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf(redefinition_k2_relset_1, axiom,
% 7.69/7.92    (![A:$i,B:$i,C:$i]:
% 7.69/7.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.69/7.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 7.69/7.92  thf('11', plain,
% 7.69/7.92      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.69/7.92         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 7.69/7.92          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 7.69/7.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.69/7.92  thf('12', plain,
% 7.69/7.92      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 7.69/7.92         = (k2_relat_1 @ sk_C))),
% 7.69/7.92      inference('sup-', [status(thm)], ['10', '11'])).
% 7.69/7.92  thf('13', plain,
% 7.69/7.92      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 7.69/7.92         = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('14', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('15', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('16', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('17', plain,
% 7.69/7.92      (((m1_subset_1 @ sk_C @ 
% 7.69/7.92         (k1_zfmisc_1 @ 
% 7.69/7.92          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 7.69/7.92        | ~ (l1_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['15', '16'])).
% 7.69/7.92  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('19', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('demod', [status(thm)], ['17', '18'])).
% 7.69/7.92  thf('20', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('21', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 7.69/7.92      inference('demod', [status(thm)], ['19', '20'])).
% 7.69/7.92  thf(cc5_funct_2, axiom,
% 7.69/7.92    (![A:$i,B:$i]:
% 7.69/7.92     ( ( ~( v1_xboole_0 @ B ) ) =>
% 7.69/7.92       ( ![C:$i]:
% 7.69/7.92         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.69/7.92           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 7.69/7.92             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 7.69/7.92  thf('22', plain,
% 7.69/7.92      (![X37 : $i, X38 : $i, X39 : $i]:
% 7.69/7.92         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 7.69/7.92          | (v1_partfun1 @ X37 @ X38)
% 7.69/7.92          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 7.69/7.92          | ~ (v1_funct_1 @ X37)
% 7.69/7.92          | (v1_xboole_0 @ X39))),
% 7.69/7.92      inference('cnf', [status(esa)], [cc5_funct_2])).
% 7.69/7.92  thf('23', plain,
% 7.69/7.92      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 7.69/7.92        | ~ (v1_funct_1 @ sk_C)
% 7.69/7.92        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 7.69/7.92        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 7.69/7.92      inference('sup-', [status(thm)], ['21', '22'])).
% 7.69/7.92  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('25', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('26', plain,
% 7.69/7.92      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('27', plain,
% 7.69/7.92      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 7.69/7.92        | ~ (l1_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['25', '26'])).
% 7.69/7.92  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('29', plain,
% 7.69/7.92      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('demod', [status(thm)], ['27', '28'])).
% 7.69/7.92  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('31', plain,
% 7.69/7.92      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['29', '30'])).
% 7.69/7.92  thf('32', plain,
% 7.69/7.92      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 7.69/7.92        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 7.69/7.92      inference('demod', [status(thm)], ['23', '24', '31'])).
% 7.69/7.92  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf(fc5_struct_0, axiom,
% 7.69/7.92    (![A:$i]:
% 7.69/7.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 7.69/7.92       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 7.69/7.92  thf('34', plain,
% 7.69/7.92      (![X43 : $i]:
% 7.69/7.92         (~ (v1_xboole_0 @ (k2_struct_0 @ X43))
% 7.69/7.92          | ~ (l1_struct_0 @ X43)
% 7.69/7.92          | (v2_struct_0 @ X43))),
% 7.69/7.92      inference('cnf', [status(esa)], [fc5_struct_0])).
% 7.69/7.92  thf('35', plain,
% 7.69/7.92      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 7.69/7.92        | (v2_struct_0 @ sk_B)
% 7.69/7.92        | ~ (l1_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup-', [status(thm)], ['33', '34'])).
% 7.69/7.92  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('37', plain,
% 7.69/7.92      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 7.69/7.92      inference('demod', [status(thm)], ['35', '36'])).
% 7.69/7.92  thf('38', plain, (~ (v2_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('39', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 7.69/7.92      inference('clc', [status(thm)], ['37', '38'])).
% 7.69/7.92  thf('40', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 7.69/7.92      inference('clc', [status(thm)], ['32', '39'])).
% 7.69/7.92  thf(d4_partfun1, axiom,
% 7.69/7.92    (![A:$i,B:$i]:
% 7.69/7.92     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 7.69/7.92       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 7.69/7.92  thf('41', plain,
% 7.69/7.92      (![X40 : $i, X41 : $i]:
% 7.69/7.92         (~ (v1_partfun1 @ X41 @ X40)
% 7.69/7.92          | ((k1_relat_1 @ X41) = (X40))
% 7.69/7.92          | ~ (v4_relat_1 @ X41 @ X40)
% 7.69/7.92          | ~ (v1_relat_1 @ X41))),
% 7.69/7.92      inference('cnf', [status(esa)], [d4_partfun1])).
% 7.69/7.92  thf('42', plain,
% 7.69/7.92      ((~ (v1_relat_1 @ sk_C)
% 7.69/7.92        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 7.69/7.92        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 7.69/7.92      inference('sup-', [status(thm)], ['40', '41'])).
% 7.69/7.92  thf('43', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf(cc2_relat_1, axiom,
% 7.69/7.92    (![A:$i]:
% 7.69/7.92     ( ( v1_relat_1 @ A ) =>
% 7.69/7.92       ( ![B:$i]:
% 7.69/7.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 7.69/7.92  thf('44', plain,
% 7.69/7.92      (![X6 : $i, X7 : $i]:
% 7.69/7.92         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 7.69/7.92          | (v1_relat_1 @ X6)
% 7.69/7.92          | ~ (v1_relat_1 @ X7))),
% 7.69/7.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 7.69/7.92  thf('45', plain,
% 7.69/7.92      ((~ (v1_relat_1 @ 
% 7.69/7.92           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 7.69/7.92        | (v1_relat_1 @ sk_C))),
% 7.69/7.92      inference('sup-', [status(thm)], ['43', '44'])).
% 7.69/7.92  thf(fc6_relat_1, axiom,
% 7.69/7.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 7.69/7.92  thf('46', plain,
% 7.69/7.92      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 7.69/7.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 7.69/7.92  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf('48', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf(cc2_relset_1, axiom,
% 7.69/7.92    (![A:$i,B:$i,C:$i]:
% 7.69/7.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.69/7.92       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.69/7.92  thf('49', plain,
% 7.69/7.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 7.69/7.92         ((v4_relat_1 @ X22 @ X23)
% 7.69/7.92          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 7.69/7.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.69/7.92  thf('50', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 7.69/7.92      inference('sup-', [status(thm)], ['48', '49'])).
% 7.69/7.92  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 7.69/7.92      inference('demod', [status(thm)], ['42', '47', '50'])).
% 7.69/7.92  thf('52', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 7.69/7.92      inference('demod', [status(thm)], ['42', '47', '50'])).
% 7.69/7.92  thf('53', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('54', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 7.69/7.92      inference('sup-', [status(thm)], ['48', '49'])).
% 7.69/7.92  thf(t209_relat_1, axiom,
% 7.69/7.92    (![A:$i,B:$i]:
% 7.69/7.92     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 7.69/7.92       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 7.69/7.92  thf('55', plain,
% 7.69/7.92      (![X14 : $i, X15 : $i]:
% 7.69/7.92         (((X14) = (k7_relat_1 @ X14 @ X15))
% 7.69/7.92          | ~ (v4_relat_1 @ X14 @ X15)
% 7.69/7.92          | ~ (v1_relat_1 @ X14))),
% 7.69/7.92      inference('cnf', [status(esa)], [t209_relat_1])).
% 7.69/7.92  thf('56', plain,
% 7.69/7.92      ((~ (v1_relat_1 @ sk_C)
% 7.69/7.92        | ((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['54', '55'])).
% 7.69/7.92  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf('58', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 7.69/7.92      inference('demod', [status(thm)], ['56', '57'])).
% 7.69/7.92  thf(t148_relat_1, axiom,
% 7.69/7.92    (![A:$i,B:$i]:
% 7.69/7.92     ( ( v1_relat_1 @ B ) =>
% 7.69/7.92       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 7.69/7.92  thf('59', plain,
% 7.69/7.92      (![X11 : $i, X12 : $i]:
% 7.69/7.92         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 7.69/7.92          | ~ (v1_relat_1 @ X11))),
% 7.69/7.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.69/7.92  thf(t21_relat_1, axiom,
% 7.69/7.92    (![A:$i]:
% 7.69/7.92     ( ( v1_relat_1 @ A ) =>
% 7.69/7.92       ( r1_tarski @
% 7.69/7.92         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 7.69/7.92  thf('60', plain,
% 7.69/7.92      (![X16 : $i]:
% 7.69/7.92         ((r1_tarski @ X16 @ 
% 7.69/7.92           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 7.69/7.92          | ~ (v1_relat_1 @ X16))),
% 7.69/7.92      inference('cnf', [status(esa)], [t21_relat_1])).
% 7.69/7.92  thf('61', plain,
% 7.69/7.92      (![X0 : $i, X1 : $i]:
% 7.69/7.92         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 7.69/7.92           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 7.69/7.92            (k9_relat_1 @ X1 @ X0)))
% 7.69/7.92          | ~ (v1_relat_1 @ X1)
% 7.69/7.92          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 7.69/7.92      inference('sup+', [status(thm)], ['59', '60'])).
% 7.69/7.92  thf('62', plain,
% 7.69/7.92      ((~ (v1_relat_1 @ sk_C)
% 7.69/7.92        | ~ (v1_relat_1 @ sk_C)
% 7.69/7.92        | (r1_tarski @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) @ 
% 7.69/7.92           (k2_zfmisc_1 @ 
% 7.69/7.92            (k1_relat_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))) @ 
% 7.69/7.92            (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['58', '61'])).
% 7.69/7.92  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf('65', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 7.69/7.92      inference('demod', [status(thm)], ['56', '57'])).
% 7.69/7.92  thf('66', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 7.69/7.92      inference('demod', [status(thm)], ['56', '57'])).
% 7.69/7.92  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf(d9_funct_1, axiom,
% 7.69/7.92    (![A:$i]:
% 7.69/7.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.69/7.92       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 7.69/7.92  thf('68', plain,
% 7.69/7.92      (![X17 : $i]:
% 7.69/7.92         (~ (v2_funct_1 @ X17)
% 7.69/7.92          | ((k2_funct_1 @ X17) = (k4_relat_1 @ X17))
% 7.69/7.92          | ~ (v1_funct_1 @ X17)
% 7.69/7.92          | ~ (v1_relat_1 @ X17))),
% 7.69/7.92      inference('cnf', [status(esa)], [d9_funct_1])).
% 7.69/7.92  thf('69', plain,
% 7.69/7.92      ((~ (v1_funct_1 @ sk_C)
% 7.69/7.92        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 7.69/7.92        | ~ (v2_funct_1 @ sk_C))),
% 7.69/7.92      inference('sup-', [status(thm)], ['67', '68'])).
% 7.69/7.92  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('72', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['69', '70', '71'])).
% 7.69/7.92  thf(t154_funct_1, axiom,
% 7.69/7.92    (![A:$i,B:$i]:
% 7.69/7.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 7.69/7.92       ( ( v2_funct_1 @ B ) =>
% 7.69/7.92         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 7.69/7.92  thf('73', plain,
% 7.69/7.92      (![X18 : $i, X19 : $i]:
% 7.69/7.92         (~ (v2_funct_1 @ X18)
% 7.69/7.92          | ((k9_relat_1 @ X18 @ X19)
% 7.69/7.92              = (k10_relat_1 @ (k2_funct_1 @ X18) @ X19))
% 7.69/7.92          | ~ (v1_funct_1 @ X18)
% 7.69/7.92          | ~ (v1_relat_1 @ X18))),
% 7.69/7.92      inference('cnf', [status(esa)], [t154_funct_1])).
% 7.69/7.92  thf('74', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         (((k9_relat_1 @ sk_C @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ X0))
% 7.69/7.92          | ~ (v1_relat_1 @ sk_C)
% 7.69/7.92          | ~ (v1_funct_1 @ sk_C)
% 7.69/7.92          | ~ (v2_funct_1 @ sk_C))),
% 7.69/7.92      inference('sup+', [status(thm)], ['72', '73'])).
% 7.69/7.92  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('78', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         ((k9_relat_1 @ sk_C @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ X0))),
% 7.69/7.92      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 7.69/7.92  thf('79', plain,
% 7.69/7.92      ((r1_tarski @ sk_C @ 
% 7.69/7.92        (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ 
% 7.69/7.92         (k10_relat_1 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 7.69/7.92      inference('demod', [status(thm)], ['62', '63', '64', '65', '66', '78'])).
% 7.69/7.92  thf('80', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 7.69/7.92      inference('demod', [status(thm)], ['56', '57'])).
% 7.69/7.92  thf('81', plain,
% 7.69/7.92      (![X11 : $i, X12 : $i]:
% 7.69/7.92         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 7.69/7.92          | ~ (v1_relat_1 @ X11))),
% 7.69/7.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.69/7.92  thf('82', plain,
% 7.69/7.92      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 7.69/7.92        | ~ (v1_relat_1 @ sk_C))),
% 7.69/7.92      inference('sup+', [status(thm)], ['80', '81'])).
% 7.69/7.92  thf('83', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         ((k9_relat_1 @ sk_C @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ X0))),
% 7.69/7.92      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 7.69/7.92  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf('85', plain,
% 7.69/7.92      (((k2_relat_1 @ sk_C)
% 7.69/7.92         = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 7.69/7.92      inference('demod', [status(thm)], ['82', '83', '84'])).
% 7.69/7.92  thf('86', plain,
% 7.69/7.92      ((r1_tarski @ sk_C @ 
% 7.69/7.92        (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)], ['79', '85'])).
% 7.69/7.92  thf(t3_subset, axiom,
% 7.69/7.92    (![A:$i,B:$i]:
% 7.69/7.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.69/7.92  thf('87', plain,
% 7.69/7.92      (![X3 : $i, X5 : $i]:
% 7.69/7.92         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 7.69/7.92      inference('cnf', [status(esa)], [t3_subset])).
% 7.69/7.92  thf('88', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['86', '87'])).
% 7.69/7.92  thf(d4_tops_2, axiom,
% 7.69/7.92    (![A:$i,B:$i,C:$i]:
% 7.69/7.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.69/7.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.69/7.92       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 7.69/7.92         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 7.69/7.92  thf('89', plain,
% 7.69/7.92      (![X44 : $i, X45 : $i, X46 : $i]:
% 7.69/7.92         (((k2_relset_1 @ X45 @ X44 @ X46) != (X44))
% 7.69/7.92          | ~ (v2_funct_1 @ X46)
% 7.69/7.92          | ((k2_tops_2 @ X45 @ X44 @ X46) = (k2_funct_1 @ X46))
% 7.69/7.92          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 7.69/7.92          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 7.69/7.92          | ~ (v1_funct_1 @ X46))),
% 7.69/7.92      inference('cnf', [status(esa)], [d4_tops_2])).
% 7.69/7.92  thf('90', plain,
% 7.69/7.92      ((~ (v1_funct_1 @ sk_C)
% 7.69/7.92        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 7.69/7.92        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92            = (k2_funct_1 @ sk_C))
% 7.69/7.92        | ~ (v2_funct_1 @ sk_C)
% 7.69/7.92        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92            != (k2_relat_1 @ sk_C)))),
% 7.69/7.92      inference('sup-', [status(thm)], ['88', '89'])).
% 7.69/7.92  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('92', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('93', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('94', plain,
% 7.69/7.92      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('95', plain,
% 7.69/7.92      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 7.69/7.92        | ~ (l1_struct_0 @ sk_A))),
% 7.69/7.92      inference('sup+', [status(thm)], ['93', '94'])).
% 7.69/7.92  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('97', plain,
% 7.69/7.92      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 7.69/7.92      inference('demod', [status(thm)], ['95', '96'])).
% 7.69/7.92  thf('98', plain,
% 7.69/7.92      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 7.69/7.92        | ~ (l1_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['92', '97'])).
% 7.69/7.92  thf('99', plain, ((l1_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('100', plain,
% 7.69/7.92      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('demod', [status(thm)], ['98', '99'])).
% 7.69/7.92  thf('101', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('102', plain,
% 7.69/7.92      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['100', '101'])).
% 7.69/7.92  thf('103', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('104', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 7.69/7.92      inference('clc', [status(thm)], ['32', '39'])).
% 7.69/7.92  thf('105', plain,
% 7.69/7.92      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 7.69/7.92      inference('sup+', [status(thm)], ['103', '104'])).
% 7.69/7.92  thf('106', plain, ((l1_struct_0 @ sk_A)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('107', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 7.69/7.92      inference('demod', [status(thm)], ['105', '106'])).
% 7.69/7.92  thf('108', plain,
% 7.69/7.92      (![X40 : $i, X41 : $i]:
% 7.69/7.92         (~ (v1_partfun1 @ X41 @ X40)
% 7.69/7.92          | ((k1_relat_1 @ X41) = (X40))
% 7.69/7.92          | ~ (v4_relat_1 @ X41 @ X40)
% 7.69/7.92          | ~ (v1_relat_1 @ X41))),
% 7.69/7.92      inference('cnf', [status(esa)], [d4_partfun1])).
% 7.69/7.92  thf('109', plain,
% 7.69/7.92      ((~ (v1_relat_1 @ sk_C)
% 7.69/7.92        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 7.69/7.92        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 7.69/7.92      inference('sup-', [status(thm)], ['107', '108'])).
% 7.69/7.92  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf('111', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('112', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('113', plain,
% 7.69/7.92      (((m1_subset_1 @ sk_C @ 
% 7.69/7.92         (k1_zfmisc_1 @ 
% 7.69/7.92          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 7.69/7.92        | ~ (l1_struct_0 @ sk_A))),
% 7.69/7.92      inference('sup+', [status(thm)], ['111', '112'])).
% 7.69/7.92  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('115', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 7.69/7.92      inference('demod', [status(thm)], ['113', '114'])).
% 7.69/7.92  thf('116', plain,
% 7.69/7.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 7.69/7.92         ((v4_relat_1 @ X22 @ X23)
% 7.69/7.92          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 7.69/7.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.69/7.92  thf('117', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 7.69/7.92      inference('sup-', [status(thm)], ['115', '116'])).
% 7.69/7.92  thf('118', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 7.69/7.92      inference('demod', [status(thm)], ['109', '110', '117'])).
% 7.69/7.92  thf('119', plain,
% 7.69/7.92      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['102', '118'])).
% 7.69/7.92  thf('120', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['69', '70', '71'])).
% 7.69/7.92  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('122', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('123', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('124', plain,
% 7.69/7.92      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 7.69/7.92         = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('125', plain,
% 7.69/7.92      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 7.69/7.92          = (k2_struct_0 @ sk_B))
% 7.69/7.92        | ~ (l1_struct_0 @ sk_A))),
% 7.69/7.92      inference('sup+', [status(thm)], ['123', '124'])).
% 7.69/7.92  thf('126', plain, ((l1_struct_0 @ sk_A)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('127', plain,
% 7.69/7.92      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 7.69/7.92         = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('demod', [status(thm)], ['125', '126'])).
% 7.69/7.92  thf('128', plain,
% 7.69/7.92      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 7.69/7.92          = (k2_struct_0 @ sk_B))
% 7.69/7.92        | ~ (l1_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['122', '127'])).
% 7.69/7.92  thf('129', plain, ((l1_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('130', plain,
% 7.69/7.92      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 7.69/7.92         = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('demod', [status(thm)], ['128', '129'])).
% 7.69/7.92  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('132', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('133', plain,
% 7.69/7.92      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92         = (k2_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['130', '131', '132'])).
% 7.69/7.92  thf('134', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 7.69/7.92      inference('demod', [status(thm)], ['109', '110', '117'])).
% 7.69/7.92  thf('135', plain,
% 7.69/7.92      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92         = (k2_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['133', '134'])).
% 7.69/7.92  thf('136', plain,
% 7.69/7.92      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92          = (k4_relat_1 @ sk_C))
% 7.69/7.92        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)],
% 7.69/7.92                ['90', '91', '119', '120', '121', '135'])).
% 7.69/7.92  thf('137', plain,
% 7.69/7.92      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92         = (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('simplify', [status(thm)], ['136'])).
% 7.69/7.92  thf('138', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['86', '87'])).
% 7.69/7.92  thf(dt_k3_relset_1, axiom,
% 7.69/7.92    (![A:$i,B:$i,C:$i]:
% 7.69/7.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.69/7.92       ( m1_subset_1 @
% 7.69/7.92         ( k3_relset_1 @ A @ B @ C ) @ 
% 7.69/7.92         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 7.69/7.92  thf('139', plain,
% 7.69/7.92      (![X25 : $i, X26 : $i, X27 : $i]:
% 7.69/7.92         ((m1_subset_1 @ (k3_relset_1 @ X25 @ X26 @ X27) @ 
% 7.69/7.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 7.69/7.92          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 7.69/7.92      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 7.69/7.92  thf('140', plain,
% 7.69/7.92      ((m1_subset_1 @ 
% 7.69/7.92        (k3_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['138', '139'])).
% 7.69/7.92  thf('141', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('142', plain,
% 7.69/7.92      ((m1_subset_1 @ sk_C @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 7.69/7.92      inference('demod', [status(thm)], ['19', '20'])).
% 7.69/7.92  thf(redefinition_k3_relset_1, axiom,
% 7.69/7.92    (![A:$i,B:$i,C:$i]:
% 7.69/7.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.69/7.92       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 7.69/7.92  thf('143', plain,
% 7.69/7.92      (![X34 : $i, X35 : $i, X36 : $i]:
% 7.69/7.92         (((k3_relset_1 @ X35 @ X36 @ X34) = (k4_relat_1 @ X34))
% 7.69/7.92          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 7.69/7.92      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 7.69/7.92  thf('144', plain,
% 7.69/7.92      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92         = (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('sup-', [status(thm)], ['142', '143'])).
% 7.69/7.92  thf('145', plain,
% 7.69/7.92      ((((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92          = (k4_relat_1 @ sk_C))
% 7.69/7.92        | ~ (l1_struct_0 @ sk_A))),
% 7.69/7.92      inference('sup+', [status(thm)], ['141', '144'])).
% 7.69/7.92  thf('146', plain, ((l1_struct_0 @ sk_A)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('147', plain,
% 7.69/7.92      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92         = (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['145', '146'])).
% 7.69/7.92  thf('148', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 7.69/7.92      inference('demod', [status(thm)], ['109', '110', '117'])).
% 7.69/7.92  thf('149', plain,
% 7.69/7.92      (((k3_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92         = (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['147', '148'])).
% 7.69/7.92  thf('150', plain,
% 7.69/7.92      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 7.69/7.92      inference('demod', [status(thm)], ['140', '149'])).
% 7.69/7.92  thf('151', plain,
% 7.69/7.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 7.69/7.92         ((v4_relat_1 @ X22 @ X23)
% 7.69/7.92          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 7.69/7.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.69/7.92  thf('152', plain, ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 7.69/7.92      inference('sup-', [status(thm)], ['150', '151'])).
% 7.69/7.92  thf('153', plain,
% 7.69/7.92      (![X14 : $i, X15 : $i]:
% 7.69/7.92         (((X14) = (k7_relat_1 @ X14 @ X15))
% 7.69/7.92          | ~ (v4_relat_1 @ X14 @ X15)
% 7.69/7.92          | ~ (v1_relat_1 @ X14))),
% 7.69/7.92      inference('cnf', [status(esa)], [t209_relat_1])).
% 7.69/7.92  thf('154', plain,
% 7.69/7.92      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 7.69/7.92        | ((k4_relat_1 @ sk_C)
% 7.69/7.92            = (k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['152', '153'])).
% 7.69/7.92  thf('155', plain,
% 7.69/7.92      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 7.69/7.92        (k1_zfmisc_1 @ 
% 7.69/7.92         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 7.69/7.92      inference('demod', [status(thm)], ['140', '149'])).
% 7.69/7.92  thf('156', plain,
% 7.69/7.92      (![X6 : $i, X7 : $i]:
% 7.69/7.92         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 7.69/7.92          | (v1_relat_1 @ X6)
% 7.69/7.92          | ~ (v1_relat_1 @ X7))),
% 7.69/7.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 7.69/7.92  thf('157', plain,
% 7.69/7.92      ((~ (v1_relat_1 @ 
% 7.69/7.92           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 7.69/7.92        | (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 7.69/7.92      inference('sup-', [status(thm)], ['155', '156'])).
% 7.69/7.92  thf('158', plain,
% 7.69/7.92      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 7.69/7.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 7.69/7.92  thf('159', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['157', '158'])).
% 7.69/7.92  thf('160', plain,
% 7.69/7.92      (((k4_relat_1 @ sk_C)
% 7.69/7.92         = (k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)], ['154', '159'])).
% 7.69/7.92  thf('161', plain,
% 7.69/7.92      (![X11 : $i, X12 : $i]:
% 7.69/7.92         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 7.69/7.92          | ~ (v1_relat_1 @ X11))),
% 7.69/7.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.69/7.92  thf(t169_relat_1, axiom,
% 7.69/7.92    (![A:$i]:
% 7.69/7.92     ( ( v1_relat_1 @ A ) =>
% 7.69/7.92       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 7.69/7.92  thf('162', plain,
% 7.69/7.92      (![X13 : $i]:
% 7.69/7.92         (((k10_relat_1 @ X13 @ (k2_relat_1 @ X13)) = (k1_relat_1 @ X13))
% 7.69/7.92          | ~ (v1_relat_1 @ X13))),
% 7.69/7.92      inference('cnf', [status(esa)], [t169_relat_1])).
% 7.69/7.92  thf('163', plain,
% 7.69/7.92      (![X0 : $i, X1 : $i]:
% 7.69/7.92         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 7.69/7.92            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 7.69/7.92          | ~ (v1_relat_1 @ X1)
% 7.69/7.92          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 7.69/7.92      inference('sup+', [status(thm)], ['161', '162'])).
% 7.69/7.92  thf('164', plain,
% 7.69/7.92      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 7.69/7.92        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 7.69/7.92        | ((k10_relat_1 @ 
% 7.69/7.92            (k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 7.69/7.92            (k9_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 7.69/7.92            = (k1_relat_1 @ 
% 7.69/7.92               (k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['160', '163'])).
% 7.69/7.92  thf('165', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['157', '158'])).
% 7.69/7.92  thf('166', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['157', '158'])).
% 7.69/7.92  thf('167', plain,
% 7.69/7.92      (((k4_relat_1 @ sk_C)
% 7.69/7.92         = (k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)], ['154', '159'])).
% 7.69/7.92  thf('168', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['69', '70', '71'])).
% 7.69/7.92  thf(d10_xboole_0, axiom,
% 7.69/7.92    (![A:$i,B:$i]:
% 7.69/7.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.69/7.92  thf('169', plain,
% 7.69/7.92      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 7.69/7.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.69/7.92  thf('170', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 7.69/7.92      inference('simplify', [status(thm)], ['169'])).
% 7.69/7.92  thf(t177_funct_1, axiom,
% 7.69/7.92    (![A:$i]:
% 7.69/7.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.69/7.92       ( ![B:$i]:
% 7.69/7.92         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 7.69/7.92           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 7.69/7.92             ( B ) ) ) ) ))).
% 7.69/7.92  thf('171', plain,
% 7.69/7.92      (![X20 : $i, X21 : $i]:
% 7.69/7.92         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 7.69/7.92          | ((k9_relat_1 @ (k2_funct_1 @ X21) @ (k9_relat_1 @ X21 @ X20))
% 7.69/7.92              = (X20))
% 7.69/7.92          | ~ (v2_funct_1 @ X21)
% 7.69/7.92          | ~ (v1_funct_1 @ X21)
% 7.69/7.92          | ~ (v1_relat_1 @ X21))),
% 7.69/7.92      inference('cnf', [status(esa)], [t177_funct_1])).
% 7.69/7.92  thf('172', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         (~ (v1_relat_1 @ X0)
% 7.69/7.92          | ~ (v1_funct_1 @ X0)
% 7.69/7.92          | ~ (v2_funct_1 @ X0)
% 7.69/7.92          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 7.69/7.92              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 7.69/7.92      inference('sup-', [status(thm)], ['170', '171'])).
% 7.69/7.92  thf('173', plain,
% 7.69/7.92      ((((k9_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 7.69/7.92          (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))) = (k1_relat_1 @ sk_C))
% 7.69/7.92        | ~ (v2_funct_1 @ sk_C)
% 7.69/7.92        | ~ (v1_funct_1 @ sk_C)
% 7.69/7.92        | ~ (v1_relat_1 @ sk_C))),
% 7.69/7.92      inference('sup+', [status(thm)], ['168', '172'])).
% 7.69/7.92  thf('174', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         ((k9_relat_1 @ sk_C @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ X0))),
% 7.69/7.92      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 7.69/7.92  thf(t146_relat_1, axiom,
% 7.69/7.92    (![A:$i]:
% 7.69/7.92     ( ( v1_relat_1 @ A ) =>
% 7.69/7.92       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 7.69/7.92  thf('175', plain,
% 7.69/7.92      (![X10 : $i]:
% 7.69/7.92         (((k9_relat_1 @ X10 @ (k1_relat_1 @ X10)) = (k2_relat_1 @ X10))
% 7.69/7.92          | ~ (v1_relat_1 @ X10))),
% 7.69/7.92      inference('cnf', [status(esa)], [t146_relat_1])).
% 7.69/7.92  thf('176', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         ((k9_relat_1 @ sk_C @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ X0))),
% 7.69/7.92      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 7.69/7.92  thf('177', plain,
% 7.69/7.92      ((((k2_relat_1 @ sk_C)
% 7.69/7.92          = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 7.69/7.92        | ~ (v1_relat_1 @ sk_C))),
% 7.69/7.92      inference('sup+', [status(thm)], ['175', '176'])).
% 7.69/7.92  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf('179', plain,
% 7.69/7.92      (((k2_relat_1 @ sk_C)
% 7.69/7.92         = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)], ['177', '178'])).
% 7.69/7.92  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 7.69/7.92      inference('demod', [status(thm)], ['45', '46'])).
% 7.69/7.92  thf('183', plain,
% 7.69/7.92      (((k9_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 7.69/7.92         = (k1_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)],
% 7.69/7.92                ['173', '174', '179', '180', '181', '182'])).
% 7.69/7.92  thf('184', plain,
% 7.69/7.92      (((k2_relat_1 @ sk_C)
% 7.69/7.92         = (k10_relat_1 @ (k4_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)], ['177', '178'])).
% 7.69/7.92  thf('185', plain,
% 7.69/7.92      (((k4_relat_1 @ sk_C)
% 7.69/7.92         = (k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)], ['154', '159'])).
% 7.69/7.92  thf('186', plain,
% 7.69/7.92      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)],
% 7.69/7.92                ['164', '165', '166', '167', '183', '184', '185'])).
% 7.69/7.92  thf('187', plain,
% 7.69/7.92      (![X16 : $i]:
% 7.69/7.92         ((r1_tarski @ X16 @ 
% 7.69/7.92           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 7.69/7.92          | ~ (v1_relat_1 @ X16))),
% 7.69/7.92      inference('cnf', [status(esa)], [t21_relat_1])).
% 7.69/7.92  thf('188', plain,
% 7.69/7.92      (![X3 : $i, X5 : $i]:
% 7.69/7.92         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 7.69/7.92      inference('cnf', [status(esa)], [t3_subset])).
% 7.69/7.92  thf('189', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         (~ (v1_relat_1 @ X0)
% 7.69/7.92          | (m1_subset_1 @ X0 @ 
% 7.69/7.92             (k1_zfmisc_1 @ 
% 7.69/7.92              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['187', '188'])).
% 7.69/7.92  thf('190', plain,
% 7.69/7.92      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.69/7.92         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 7.69/7.92          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 7.69/7.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.69/7.92  thf('191', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         (~ (v1_relat_1 @ X0)
% 7.69/7.92          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 7.69/7.92              = (k2_relat_1 @ X0)))),
% 7.69/7.92      inference('sup-', [status(thm)], ['189', '190'])).
% 7.69/7.92  thf('192', plain,
% 7.69/7.92      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ 
% 7.69/7.92          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 7.69/7.92          = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 7.69/7.92        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 7.69/7.92      inference('sup+', [status(thm)], ['186', '191'])).
% 7.69/7.92  thf('193', plain,
% 7.69/7.92      (((k4_relat_1 @ sk_C)
% 7.69/7.92         = (k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)], ['154', '159'])).
% 7.69/7.92  thf('194', plain,
% 7.69/7.92      (![X11 : $i, X12 : $i]:
% 7.69/7.92         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 7.69/7.92          | ~ (v1_relat_1 @ X11))),
% 7.69/7.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.69/7.92  thf('195', plain,
% 7.69/7.92      ((((k2_relat_1 @ (k4_relat_1 @ sk_C))
% 7.69/7.92          = (k9_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 7.69/7.92        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 7.69/7.92      inference('sup+', [status(thm)], ['193', '194'])).
% 7.69/7.92  thf('196', plain,
% 7.69/7.92      (((k9_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 7.69/7.92         = (k1_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)],
% 7.69/7.92                ['173', '174', '179', '180', '181', '182'])).
% 7.69/7.92  thf('197', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['157', '158'])).
% 7.69/7.92  thf('198', plain,
% 7.69/7.92      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['195', '196', '197'])).
% 7.69/7.92  thf('199', plain,
% 7.69/7.92      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['195', '196', '197'])).
% 7.69/7.92  thf('200', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['157', '158'])).
% 7.69/7.92  thf('201', plain,
% 7.69/7.92      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 7.69/7.92         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['192', '198', '199', '200'])).
% 7.69/7.92  thf('202', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 7.69/7.92      inference('demod', [status(thm)], ['109', '110', '117'])).
% 7.69/7.92  thf('203', plain,
% 7.69/7.92      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_A))))),
% 7.69/7.92      inference('demod', [status(thm)],
% 7.69/7.92                ['9', '14', '51', '52', '53', '137', '201', '202'])).
% 7.69/7.92  thf('204', plain,
% 7.69/7.92      (($false)
% 7.69/7.92         <= (~
% 7.69/7.92             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_A))))),
% 7.69/7.92      inference('simplify', [status(thm)], ['203'])).
% 7.69/7.92  thf('205', plain,
% 7.69/7.92      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)],
% 7.69/7.92                ['164', '165', '166', '167', '183', '184', '185'])).
% 7.69/7.92  thf('206', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         (~ (v1_relat_1 @ X0)
% 7.69/7.92          | (m1_subset_1 @ X0 @ 
% 7.69/7.92             (k1_zfmisc_1 @ 
% 7.69/7.92              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['187', '188'])).
% 7.69/7.92  thf(redefinition_k1_relset_1, axiom,
% 7.69/7.92    (![A:$i,B:$i,C:$i]:
% 7.69/7.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.69/7.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 7.69/7.92  thf('207', plain,
% 7.69/7.92      (![X28 : $i, X29 : $i, X30 : $i]:
% 7.69/7.92         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 7.69/7.92          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 7.69/7.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.69/7.92  thf('208', plain,
% 7.69/7.92      (![X0 : $i]:
% 7.69/7.92         (~ (v1_relat_1 @ X0)
% 7.69/7.92          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 7.69/7.92              = (k1_relat_1 @ X0)))),
% 7.69/7.92      inference('sup-', [status(thm)], ['206', '207'])).
% 7.69/7.92  thf('209', plain,
% 7.69/7.92      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ 
% 7.69/7.92          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 7.69/7.92          = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 7.69/7.92        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 7.69/7.92      inference('sup+', [status(thm)], ['205', '208'])).
% 7.69/7.92  thf('210', plain,
% 7.69/7.92      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['195', '196', '197'])).
% 7.69/7.92  thf('211', plain,
% 7.69/7.92      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 7.69/7.92      inference('demod', [status(thm)],
% 7.69/7.92                ['164', '165', '166', '167', '183', '184', '185'])).
% 7.69/7.92  thf('212', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['157', '158'])).
% 7.69/7.92  thf('213', plain,
% 7.69/7.92      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 7.69/7.92         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 7.69/7.92      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 7.69/7.92  thf('214', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('215', plain,
% 7.69/7.92      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 7.69/7.92         = (k4_relat_1 @ sk_C))),
% 7.69/7.92      inference('simplify', [status(thm)], ['136'])).
% 7.69/7.92  thf('216', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('217', plain,
% 7.69/7.92      (![X42 : $i]:
% 7.69/7.92         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 7.69/7.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.69/7.92  thf('218', plain,
% 7.69/7.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          != (k2_struct_0 @ sk_B)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('split', [status(esa)], ['2'])).
% 7.69/7.92  thf('219', plain,
% 7.69/7.92      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92           != (k2_struct_0 @ sk_B))
% 7.69/7.92         | ~ (l1_struct_0 @ sk_B)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['217', '218'])).
% 7.69/7.92  thf('220', plain, ((l1_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('221', plain,
% 7.69/7.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          != (k2_struct_0 @ sk_B)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('demod', [status(thm)], ['219', '220'])).
% 7.69/7.92  thf('222', plain,
% 7.69/7.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 7.69/7.92          != (k2_struct_0 @ sk_B)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['216', '221'])).
% 7.69/7.92  thf('223', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('224', plain,
% 7.69/7.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 7.69/7.92          != (k2_relat_1 @ sk_C)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('demod', [status(thm)], ['222', '223'])).
% 7.69/7.92  thf('225', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 7.69/7.92      inference('demod', [status(thm)], ['42', '47', '50'])).
% 7.69/7.92  thf('226', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 7.69/7.92      inference('demod', [status(thm)], ['42', '47', '50'])).
% 7.69/7.92  thf('227', plain,
% 7.69/7.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 7.69/7.92          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 7.69/7.92          != (k2_relat_1 @ sk_C)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('demod', [status(thm)], ['224', '225', '226'])).
% 7.69/7.92  thf('228', plain,
% 7.69/7.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 7.69/7.92          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['215', '227'])).
% 7.69/7.92  thf('229', plain,
% 7.69/7.92      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 7.69/7.92           (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 7.69/7.92         | ~ (l1_struct_0 @ sk_B)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['214', '228'])).
% 7.69/7.92  thf('230', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 7.69/7.92      inference('sup+', [status(thm)], ['12', '13'])).
% 7.69/7.92  thf('231', plain, ((l1_struct_0 @ sk_B)),
% 7.69/7.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.92  thf('232', plain,
% 7.69/7.92      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 7.69/7.92          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('demod', [status(thm)], ['229', '230', '231'])).
% 7.69/7.92  thf('233', plain,
% 7.69/7.92      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 7.69/7.92         <= (~
% 7.69/7.92             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92                = (k2_struct_0 @ sk_B))))),
% 7.69/7.92      inference('sup-', [status(thm)], ['213', '232'])).
% 7.69/7.92  thf('234', plain,
% 7.69/7.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          = (k2_struct_0 @ sk_B)))),
% 7.69/7.92      inference('simplify', [status(thm)], ['233'])).
% 7.69/7.92  thf('235', plain,
% 7.69/7.92      (~
% 7.69/7.92       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          = (k2_struct_0 @ sk_A))) | 
% 7.69/7.92       ~
% 7.69/7.92       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          = (k2_struct_0 @ sk_B)))),
% 7.69/7.92      inference('split', [status(esa)], ['2'])).
% 7.69/7.92  thf('236', plain,
% 7.69/7.92      (~
% 7.69/7.92       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 7.69/7.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 7.69/7.92          = (k2_struct_0 @ sk_A)))),
% 7.69/7.92      inference('sat_resolution*', [status(thm)], ['234', '235'])).
% 7.69/7.92  thf('237', plain, ($false),
% 7.69/7.92      inference('simpl_trail', [status(thm)], ['204', '236'])).
% 7.69/7.92  
% 7.69/7.92  % SZS output end Refutation
% 7.69/7.92  
% 7.69/7.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
