%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4F8toMkTWx

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:57 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  231 ( 667 expanded)
%              Number of leaves         :   39 ( 213 expanded)
%              Depth                    :   24
%              Number of atoms          : 2223 (17579 expanded)
%              Number of equality atoms :  182 (1037 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

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

thf('1',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X22 @ X24 )
       != X22 )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_tops_2 @ X23 @ X22 @ X24 )
        = ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','12'])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('16',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','20'])).

thf('22',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('23',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relset_1 @ X16 @ X15 @ X14 )
       != X15 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('47',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','39','47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('54',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('58',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('70',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X22 @ X24 )
       != X22 )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_tops_2 @ X23 @ X22 @ X24 )
        = ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('108',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84','95','96','108'])).

thf('110',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','110'])).

thf('112',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','111'])).

thf('113',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('115',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','116','117','118'])).

thf('120',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('122',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['120','121'])).

thf('123',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['21','122'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('124',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('125',plain,(
    ! [X13: $i] :
      ( ( k6_partfun1 @ X13 )
      = ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('126',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('129',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X17 ) ) )
      | ( ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) )
        = ( k6_partfun1 @ X19 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X19 @ X17 @ X18 )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('130',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131','132','133','134'])).

thf('136',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['127','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('138',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['126','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('147',plain,(
    ! [X13: $i] :
      ( ( k6_partfun1 @ X13 )
      = ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('151',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','150'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('152',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('153',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('154',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('155',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','158'])).

thf('160',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('162',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','164'])).

thf('166',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relset_1 @ X16 @ X15 @ X14 )
       != X15 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['166','174'])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('177',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('181',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('183',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['165','183'])).

thf('185',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['185','186','187','188'])).

thf('190',plain,(
    $false ),
    inference(simplify,[status(thm)],['189'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4F8toMkTWx
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:52:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 523 iterations in 0.160s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.61  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.36/0.61  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.36/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.61  thf(t55_funct_1, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.61       ( ( v2_funct_1 @ A ) =>
% 0.36/0.61         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.36/0.61           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.36/0.61  thf('0', plain,
% 0.36/0.61      (![X2 : $i]:
% 0.36/0.61         (~ (v2_funct_1 @ X2)
% 0.36/0.61          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 0.36/0.61          | ~ (v1_funct_1 @ X2)
% 0.36/0.61          | ~ (v1_relat_1 @ X2))),
% 0.36/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.61  thf(t62_tops_2, conjecture,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( l1_struct_0 @ A ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.36/0.61           ( ![C:$i]:
% 0.36/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.61                 ( m1_subset_1 @
% 0.36/0.61                   C @ 
% 0.36/0.61                   ( k1_zfmisc_1 @
% 0.36/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.61               ( ( ( ( k2_relset_1 @
% 0.36/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.61                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.61                   ( v2_funct_1 @ C ) ) =>
% 0.36/0.61                 ( ( ( k1_relset_1 @
% 0.36/0.61                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.61                       ( k2_tops_2 @
% 0.36/0.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.61                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.61                   ( ( k2_relset_1 @
% 0.36/0.61                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.61                       ( k2_tops_2 @
% 0.36/0.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.61                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i]:
% 0.36/0.61        ( ( l1_struct_0 @ A ) =>
% 0.36/0.61          ( ![B:$i]:
% 0.36/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.36/0.61              ( ![C:$i]:
% 0.36/0.61                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.61                    ( v1_funct_2 @
% 0.36/0.61                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.61                    ( m1_subset_1 @
% 0.36/0.61                      C @ 
% 0.36/0.61                      ( k1_zfmisc_1 @
% 0.36/0.61                        ( k2_zfmisc_1 @
% 0.36/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.61                  ( ( ( ( k2_relset_1 @
% 0.36/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.61                        ( k2_struct_0 @ B ) ) & 
% 0.36/0.61                      ( v2_funct_1 @ C ) ) =>
% 0.36/0.61                    ( ( ( k1_relset_1 @
% 0.36/0.61                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.61                          ( k2_tops_2 @
% 0.36/0.61                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.61                        ( k2_struct_0 @ B ) ) & 
% 0.36/0.61                      ( ( k2_relset_1 @
% 0.36/0.61                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.61                          ( k2_tops_2 @
% 0.36/0.61                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.61                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.36/0.61  thf('1', plain,
% 0.36/0.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61          != (k2_struct_0 @ sk_B))
% 0.36/0.61        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61            != (k2_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('2', plain,
% 0.36/0.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61          != (k2_struct_0 @ sk_A)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_A))))),
% 0.36/0.61      inference('split', [status(esa)], ['1'])).
% 0.36/0.61  thf(d3_struct_0, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.61  thf('3', plain,
% 0.36/0.61      (![X20 : $i]:
% 0.36/0.61         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.61  thf('4', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(d4_tops_2, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.61       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.61         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.36/0.61  thf('5', plain,
% 0.36/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.61         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.36/0.61          | ~ (v2_funct_1 @ X24)
% 0.36/0.61          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.36/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.36/0.61          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.36/0.61          | ~ (v1_funct_1 @ X24))),
% 0.36/0.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.61  thf('6', plain,
% 0.36/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.61        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61            = (k2_funct_1 @ sk_C))
% 0.36/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.61        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61            != (u1_struct_0 @ sk_B)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.61  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('8', plain,
% 0.36/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('9', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('10', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.61  thf('11', plain,
% 0.36/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.61         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.36/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.61  thf('12', plain,
% 0.36/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61         = (k2_relat_1 @ sk_C))),
% 0.36/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.61  thf('13', plain,
% 0.36/0.61      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61          = (k2_funct_1 @ sk_C))
% 0.36/0.61        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.36/0.61      inference('demod', [status(thm)], ['6', '7', '8', '9', '12'])).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.36/0.61        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.61        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61            = (k2_funct_1 @ sk_C)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['3', '13'])).
% 0.36/0.61  thf('15', plain,
% 0.36/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61         = (k2_relat_1 @ sk_C))),
% 0.36/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61         = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('17', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.61  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('19', plain,
% 0.36/0.61      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.61        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61            = (k2_funct_1 @ sk_C)))),
% 0.36/0.61      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.36/0.61  thf('20', plain,
% 0.36/0.61      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61         = (k2_funct_1 @ sk_C))),
% 0.36/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.61  thf('21', plain,
% 0.36/0.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_A))))),
% 0.36/0.61      inference('demod', [status(thm)], ['2', '20'])).
% 0.36/0.61  thf('22', plain,
% 0.36/0.61      (![X2 : $i]:
% 0.36/0.61         (~ (v2_funct_1 @ X2)
% 0.36/0.61          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.36/0.61          | ~ (v1_funct_1 @ X2)
% 0.36/0.61          | ~ (v1_relat_1 @ X2))),
% 0.36/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.61  thf('23', plain,
% 0.36/0.61      (![X20 : $i]:
% 0.36/0.61         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.61  thf('24', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('25', plain,
% 0.36/0.61      (((m1_subset_1 @ sk_C @ 
% 0.36/0.61         (k1_zfmisc_1 @ 
% 0.36/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.36/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['23', '24'])).
% 0.36/0.61  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('27', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.61  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.61  thf('29', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.61      inference('demod', [status(thm)], ['27', '28'])).
% 0.36/0.61  thf(t31_funct_2, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.61       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.36/0.61         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.36/0.61           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.36/0.61           ( m1_subset_1 @
% 0.36/0.61             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.36/0.61  thf('30', plain,
% 0.36/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.61         (~ (v2_funct_1 @ X14)
% 0.36/0.61          | ((k2_relset_1 @ X16 @ X15 @ X14) != (X15))
% 0.36/0.61          | (m1_subset_1 @ (k2_funct_1 @ X14) @ 
% 0.36/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.36/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.36/0.61          | ~ (v1_funct_2 @ X14 @ X16 @ X15)
% 0.36/0.61          | ~ (v1_funct_1 @ X14))),
% 0.36/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.61  thf('31', plain,
% 0.36/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.36/0.61        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.61           (k1_zfmisc_1 @ 
% 0.36/0.61            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.36/0.61        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.61            != (k2_relat_1 @ sk_C))
% 0.36/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.61  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('33', plain,
% 0.36/0.61      (![X20 : $i]:
% 0.36/0.61         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.61  thf('34', plain,
% 0.36/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('35', plain,
% 0.36/0.61      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['33', '34'])).
% 0.36/0.61  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('37', plain,
% 0.36/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.61  thf('38', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.61  thf('39', plain,
% 0.36/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['37', '38'])).
% 0.36/0.61  thf('40', plain,
% 0.36/0.61      (![X20 : $i]:
% 0.36/0.61         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.61  thf('41', plain,
% 0.36/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61         = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('42', plain,
% 0.36/0.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61          = (k2_struct_0 @ sk_B))
% 0.36/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.61  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('44', plain,
% 0.36/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.61         = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.61  thf('45', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.61  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.61  thf('47', plain,
% 0.36/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.61         = (k2_relat_1 @ sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.61  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('49', plain,
% 0.36/0.61      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.61         (k1_zfmisc_1 @ 
% 0.36/0.61          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.36/0.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.61      inference('demod', [status(thm)], ['31', '32', '39', '47', '48'])).
% 0.36/0.61  thf('50', plain,
% 0.36/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.61      inference('simplify', [status(thm)], ['49'])).
% 0.36/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.61  thf('51', plain,
% 0.36/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.61         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.36/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.61  thf('52', plain,
% 0.36/0.61      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.61  thf('53', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.61  thf('54', plain,
% 0.36/0.61      (![X20 : $i]:
% 0.36/0.61         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.61  thf('55', plain,
% 0.36/0.61      (![X20 : $i]:
% 0.36/0.61         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.61  thf('56', plain,
% 0.36/0.61      (![X20 : $i]:
% 0.36/0.61         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.61  thf('57', plain,
% 0.36/0.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61          != (k2_struct_0 @ sk_B)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('split', [status(esa)], ['1'])).
% 0.36/0.61  thf('58', plain,
% 0.36/0.61      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61           != (k2_struct_0 @ sk_B))
% 0.36/0.61         | ~ (l1_struct_0 @ sk_B)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.61  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('60', plain,
% 0.36/0.61      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61          != (k2_struct_0 @ sk_B)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.61  thf('61', plain,
% 0.36/0.61      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61           != (k2_struct_0 @ sk_B))
% 0.36/0.61         | ~ (l1_struct_0 @ sk_A)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['55', '60'])).
% 0.36/0.61  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('63', plain,
% 0.36/0.61      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61          != (k2_struct_0 @ sk_B)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('demod', [status(thm)], ['61', '62'])).
% 0.36/0.61  thf('64', plain,
% 0.36/0.61      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61           != (k2_struct_0 @ sk_B))
% 0.36/0.61         | ~ (l1_struct_0 @ sk_B)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['54', '63'])).
% 0.36/0.61  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('66', plain,
% 0.36/0.61      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61          != (k2_struct_0 @ sk_B)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.36/0.61  thf('67', plain,
% 0.36/0.61      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.36/0.61          != (k2_struct_0 @ sk_B)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('sup-', [status(thm)], ['53', '66'])).
% 0.36/0.61  thf('68', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.61  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.61  thf('70', plain,
% 0.36/0.61      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.36/0.61          != (k2_relat_1 @ sk_C)))
% 0.36/0.61         <= (~
% 0.36/0.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61                = (k2_struct_0 @ sk_B))))),
% 0.36/0.61      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.36/0.61  thf('71', plain,
% 0.36/0.61      (![X20 : $i]:
% 0.36/0.61         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.61  thf('72', plain,
% 0.36/0.61      (![X20 : $i]:
% 0.36/0.61         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.61  thf('73', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('74', plain,
% 0.36/0.61      (((m1_subset_1 @ sk_C @ 
% 0.36/0.61         (k1_zfmisc_1 @ 
% 0.36/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.36/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.61      inference('sup+', [status(thm)], ['72', '73'])).
% 0.36/0.62  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('76', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['74', '75'])).
% 0.36/0.62  thf('77', plain,
% 0.36/0.62      (((m1_subset_1 @ sk_C @ 
% 0.36/0.62         (k1_zfmisc_1 @ 
% 0.36/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['71', '76'])).
% 0.36/0.62  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('79', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['77', '78'])).
% 0.36/0.62  thf('80', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('81', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)], ['79', '80'])).
% 0.36/0.62  thf('82', plain,
% 0.36/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.62         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.36/0.62          | ~ (v2_funct_1 @ X24)
% 0.36/0.62          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.36/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.36/0.62          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.36/0.62          | ~ (v1_funct_1 @ X24))),
% 0.36/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.62  thf('83', plain,
% 0.36/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.36/0.62        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62            = (k2_funct_1 @ sk_C))
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62            != (k2_relat_1 @ sk_C)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['81', '82'])).
% 0.36/0.62  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('85', plain,
% 0.36/0.62      (![X20 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('86', plain,
% 0.36/0.62      (![X20 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('87', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('88', plain,
% 0.36/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup+', [status(thm)], ['86', '87'])).
% 0.36/0.62  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('90', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['88', '89'])).
% 0.36/0.62  thf('91', plain,
% 0.36/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['85', '90'])).
% 0.36/0.62  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('93', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['91', '92'])).
% 0.36/0.62  thf('94', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('95', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['93', '94'])).
% 0.36/0.62  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('97', plain,
% 0.36/0.62      (![X20 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('98', plain,
% 0.36/0.62      (![X20 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('99', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('100', plain,
% 0.36/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62          = (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup+', [status(thm)], ['98', '99'])).
% 0.36/0.62  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('102', plain,
% 0.36/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['100', '101'])).
% 0.36/0.62  thf('103', plain,
% 0.36/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62          = (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['97', '102'])).
% 0.36/0.62  thf('104', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('105', plain,
% 0.36/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['103', '104'])).
% 0.36/0.62  thf('106', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('107', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('108', plain,
% 0.36/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.36/0.62  thf('109', plain,
% 0.36/0.62      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62          = (k2_funct_1 @ sk_C))
% 0.36/0.62        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['83', '84', '95', '96', '108'])).
% 0.36/0.62  thf('110', plain,
% 0.36/0.62      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62         = (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['109'])).
% 0.36/0.62  thf('111', plain,
% 0.36/0.62      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.36/0.62         <= (~
% 0.36/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.62                = (k2_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['70', '110'])).
% 0.36/0.62  thf('112', plain,
% 0.36/0.62      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.36/0.62         <= (~
% 0.36/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.62                = (k2_struct_0 @ sk_B))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['52', '111'])).
% 0.36/0.62  thf('113', plain,
% 0.36/0.62      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.62         | ~ (v1_relat_1 @ sk_C)
% 0.36/0.62         | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62         | ~ (v2_funct_1 @ sk_C)))
% 0.36/0.62         <= (~
% 0.36/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.62                = (k2_struct_0 @ sk_B))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['22', '112'])).
% 0.36/0.62  thf('114', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(cc1_relset_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.62       ( v1_relat_1 @ C ) ))).
% 0.36/0.62  thf('115', plain,
% 0.36/0.62      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.62         ((v1_relat_1 @ X4)
% 0.36/0.62          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.36/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.62  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.36/0.62  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('119', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.36/0.62         <= (~
% 0.36/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.62                = (k2_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['113', '116', '117', '118'])).
% 0.36/0.62  thf('120', plain,
% 0.36/0.62      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.62          = (k2_struct_0 @ sk_B)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['119'])).
% 0.36/0.62  thf('121', plain,
% 0.36/0.62      (~
% 0.36/0.62       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.62          = (k2_struct_0 @ sk_A))) | 
% 0.36/0.62       ~
% 0.36/0.62       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.62          = (k2_struct_0 @ sk_B)))),
% 0.36/0.62      inference('split', [status(esa)], ['1'])).
% 0.36/0.62  thf('122', plain,
% 0.36/0.62      (~
% 0.36/0.62       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.62          = (k2_struct_0 @ sk_A)))),
% 0.36/0.62      inference('sat_resolution*', [status(thm)], ['120', '121'])).
% 0.36/0.62  thf('123', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('simpl_trail', [status(thm)], ['21', '122'])).
% 0.36/0.62  thf(t61_funct_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.62       ( ( v2_funct_1 @ A ) =>
% 0.36/0.62         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.36/0.62             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.36/0.62           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.36/0.62             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.36/0.62  thf('124', plain,
% 0.36/0.62      (![X3 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X3)
% 0.36/0.62          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 0.36/0.62              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.36/0.62          | ~ (v1_funct_1 @ X3)
% 0.36/0.62          | ~ (v1_relat_1 @ X3))),
% 0.36/0.62      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.36/0.62  thf(redefinition_k6_partfun1, axiom,
% 0.36/0.62    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.36/0.62  thf('125', plain, (![X13 : $i]: ((k6_partfun1 @ X13) = (k6_relat_1 @ X13))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.62  thf('126', plain,
% 0.36/0.62      (![X3 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X3)
% 0.36/0.62          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 0.36/0.62              = (k6_partfun1 @ (k1_relat_1 @ X3)))
% 0.36/0.62          | ~ (v1_funct_1 @ X3)
% 0.36/0.62          | ~ (v1_relat_1 @ X3))),
% 0.36/0.62      inference('demod', [status(thm)], ['124', '125'])).
% 0.36/0.62  thf('127', plain,
% 0.36/0.62      (![X20 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('128', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(t35_funct_2, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.62           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.36/0.62             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.36/0.62  thf('129', plain,
% 0.36/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.62         (((X17) = (k1_xboole_0))
% 0.36/0.62          | ~ (v1_funct_1 @ X18)
% 0.36/0.62          | ~ (v1_funct_2 @ X18 @ X19 @ X17)
% 0.36/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X17)))
% 0.36/0.62          | ((k5_relat_1 @ X18 @ (k2_funct_1 @ X18)) = (k6_partfun1 @ X19))
% 0.36/0.62          | ~ (v2_funct_1 @ X18)
% 0.36/0.62          | ((k2_relset_1 @ X19 @ X17 @ X18) != (X17)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.36/0.62  thf('130', plain,
% 0.36/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62          != (u1_struct_0 @ sk_B))
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.36/0.62            = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['128', '129'])).
% 0.36/0.62  thf('131', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.62  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('133', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('135', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B))
% 0.36/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.36/0.62            = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.62      inference('demod', [status(thm)], ['130', '131', '132', '133', '134'])).
% 0.36/0.62  thf('136', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.36/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.36/0.62            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['127', '135'])).
% 0.36/0.62  thf('137', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('138', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('139', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.36/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.36/0.62            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.62      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.36/0.62  thf('140', plain,
% 0.36/0.62      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.36/0.62          = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['139'])).
% 0.36/0.62  thf('141', plain,
% 0.36/0.62      ((((k6_partfun1 @ (k1_relat_1 @ sk_C))
% 0.36/0.62          = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['126', '140'])).
% 0.36/0.62  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.36/0.62  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('145', plain,
% 0.36/0.62      ((((k6_partfun1 @ (k1_relat_1 @ sk_C))
% 0.36/0.62          = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.62      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.36/0.62  thf(t71_relat_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.36/0.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.36/0.62  thf('146', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.62  thf('147', plain, (![X13 : $i]: ((k6_partfun1 @ X13) = (k6_relat_1 @ X13))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.62  thf('148', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['146', '147'])).
% 0.36/0.62  thf('149', plain,
% 0.36/0.62      ((((k1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.36/0.62          = (u1_struct_0 @ sk_A))
% 0.36/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['145', '148'])).
% 0.36/0.62  thf('150', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['146', '147'])).
% 0.36/0.62  thf('151', plain,
% 0.36/0.62      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.36/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.62      inference('demod', [status(thm)], ['149', '150'])).
% 0.36/0.62  thf(fc2_struct_0, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.62  thf('152', plain,
% 0.36/0.62      (![X21 : $i]:
% 0.36/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.36/0.62          | ~ (l1_struct_0 @ X21)
% 0.36/0.62          | (v2_struct_0 @ X21))),
% 0.36/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.62  thf('153', plain,
% 0.36/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.62        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.36/0.62        | (v2_struct_0 @ sk_B)
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup-', [status(thm)], ['151', '152'])).
% 0.36/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.62  thf('154', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.62  thf('155', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('156', plain,
% 0.36/0.62      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.36/0.62  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('158', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('clc', [status(thm)], ['156', '157'])).
% 0.36/0.62  thf('159', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['123', '158'])).
% 0.36/0.62  thf('160', plain,
% 0.36/0.62      (![X20 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('161', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('clc', [status(thm)], ['156', '157'])).
% 0.36/0.62  thf('162', plain,
% 0.36/0.62      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup+', [status(thm)], ['160', '161'])).
% 0.36/0.62  thf('163', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('164', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['162', '163'])).
% 0.36/0.62  thf('165', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['159', '164'])).
% 0.36/0.62  thf('166', plain,
% 0.36/0.62      (![X20 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('167', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('168', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X14)
% 0.36/0.62          | ((k2_relset_1 @ X16 @ X15 @ X14) != (X15))
% 0.36/0.62          | (m1_subset_1 @ (k2_funct_1 @ X14) @ 
% 0.36/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.36/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.36/0.62          | ~ (v1_funct_2 @ X14 @ X16 @ X15)
% 0.36/0.62          | ~ (v1_funct_1 @ X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.62  thf('169', plain,
% 0.36/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62           (k1_zfmisc_1 @ 
% 0.36/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.36/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62            != (u1_struct_0 @ sk_B))
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['167', '168'])).
% 0.36/0.62  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('171', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('172', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.62  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('174', plain,
% 0.36/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62         (k1_zfmisc_1 @ 
% 0.36/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.36/0.62        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.36/0.62      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 0.36/0.62  thf('175', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62           (k1_zfmisc_1 @ 
% 0.36/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['166', '174'])).
% 0.36/0.62  thf('176', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('177', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('178', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62           (k1_zfmisc_1 @ 
% 0.36/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.62      inference('demod', [status(thm)], ['175', '176', '177'])).
% 0.36/0.62  thf('179', plain,
% 0.36/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.62      inference('simplify', [status(thm)], ['178'])).
% 0.36/0.62  thf('180', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('clc', [status(thm)], ['156', '157'])).
% 0.36/0.62  thf('181', plain,
% 0.36/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)], ['179', '180'])).
% 0.36/0.62  thf('182', plain,
% 0.36/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.62         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.36/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.62  thf('183', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['181', '182'])).
% 0.36/0.62  thf('184', plain,
% 0.36/0.62      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['165', '183'])).
% 0.36/0.62  thf('185', plain,
% 0.36/0.62      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.36/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['0', '184'])).
% 0.36/0.62  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.36/0.62  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('189', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['185', '186', '187', '188'])).
% 0.36/0.62  thf('190', plain, ($false), inference('simplify', [status(thm)], ['189'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
