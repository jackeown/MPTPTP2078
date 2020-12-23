%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HJU5CYlvqp

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:08 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  308 (8064 expanded)
%              Number of leaves         :   38 (2319 expanded)
%              Depth                    :   35
%              Number of atoms          : 2946 (179344 expanded)
%              Number of equality atoms :  142 (5059 expanded)
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

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
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

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','13','14'])).

thf('16',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('43',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','50','57'])).

thf('59',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('68',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','58','66','67'])).

thf('69',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','50','57'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

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
    inference('sup+',[status(thm)],['11','12'])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','50','57'])).

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
    inference('sup+',[status(thm)],['11','12'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','50','57'])).

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
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['68','110'])).

thf('112',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','111'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('114',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

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

thf('117',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('118',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('121',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('122',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['118','119','120','121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
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

thf('126',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('129',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','50','57'])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('135',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','50','57'])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('138',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('139',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','50','57'])).

thf('141',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133','136','141','142'])).

thf('144',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','143'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('146',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('150',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X20 ) @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('151',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('154',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['126','148','157'])).

thf('159',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('160',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('161',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('166',plain,(
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

thf('167',plain,(
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

thf('168',plain,(
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
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
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
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
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
    inference('sup-',[status(thm)],['165','169'])).

thf('171',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['164','173'])).

thf('175',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('176',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('177',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('178',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['174','175','176','177','178'])).

thf('180',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','179'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('183',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('184',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('185',plain,(
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

thf('186',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('191',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187','188','189','190'])).

thf('192',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['183','191'])).

thf('193',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('194',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('199',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181','182','196','197','198'])).

thf('200',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','200'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('204',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('205',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('206',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('208',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('210',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != X14 )
      | ( v1_partfun1 @ X15 @ X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('211',plain,(
    ! [X15: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v4_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
      | ( v1_partfun1 @ X15 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['209','211'])).

thf('213',plain,(
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
    inference('sup-',[status(thm)],['208','212'])).

thf('214',plain,(
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
    inference('sup-',[status(thm)],['207','213'])).

thf('215',plain,(
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
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
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
    inference('sup-',[status(thm)],['206','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['205','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('223',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','50','57'])).

thf('224',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('226',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('227',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('229',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['218','219','220','221','224','227','228'])).

thf('230',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['204','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['230','231','232','233'])).

thf('235',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['203','234'])).

thf('236',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('237',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('238',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('239',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','236','237','238'])).

thf('240',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('241',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('243',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['202','243'])).

thf('245',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('246',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('247',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['244','245','246','247','248'])).

thf('250',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','249'])).

thf('251',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['115','251'])).

thf('253',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','252'])).

thf('254',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('255',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('256',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_funct_2 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['257','258','259'])).

thf('261',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['254','260'])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('264',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['261','262','263'])).

thf('265',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['48','49'])).

thf('266',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    $false ),
    inference(demod,[status(thm)],['253','264','265','266','267'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HJU5CYlvqp
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:55:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 399 iterations in 0.197s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
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
% 0.46/0.70  thf(t65_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.70       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      (![X1 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf(d3_struct_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('3', plain,
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
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70           sk_C)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70           sk_C)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['2', '7'])).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.46/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('13', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['8', '13', '14'])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.70  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('22', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.70  thf(cc5_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.70       ( ![C:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.70             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.46/0.70          | (v1_partfun1 @ X11 @ X12)
% 0.46/0.70          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.46/0.70          | ~ (v1_funct_1 @ X11)
% 0.46/0.70          | (v1_xboole_0 @ X13))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.70  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.70  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '26', '33'])).
% 0.46/0.70  thf('35', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf(fc5_struct_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.70       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (~ (v1_xboole_0 @ (k2_struct_0 @ X24))
% 0.46/0.70          | ~ (l1_struct_0 @ X24)
% 0.46/0.70          | (v2_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v2_struct_0 @ sk_B)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.70  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.70  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('41', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('clc', [status(thm)], ['39', '40'])).
% 0.46/0.70  thf('42', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('clc', [status(thm)], ['34', '41'])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['16', '42'])).
% 0.46/0.70  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('45', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.70  thf(d4_partfun1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.70       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         (~ (v1_partfun1 @ X15 @ X14)
% 0.46/0.70          | ((k1_relat_1 @ X15) = (X14))
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ X14)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( v1_relat_1 @ C ) ))).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X2)
% 0.46/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('51', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['51', '52'])).
% 0.46/0.70  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf(cc2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X5 @ X6)
% 0.46/0.70          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('57', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('58', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '50', '57'])).
% 0.46/0.70  thf('59', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('clc', [status(thm)], ['34', '41'])).
% 0.46/0.70  thf('60', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         (~ (v1_partfun1 @ X15 @ X14)
% 0.46/0.70          | ((k1_relat_1 @ X15) = (X14))
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ X14)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.70  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X5 @ X6)
% 0.46/0.70          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('65', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.70  thf('66', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.70  thf('67', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.70  thf('68', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['15', '58', '66', '67'])).
% 0.46/0.70  thf('69', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['69', '70'])).
% 0.46/0.70  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('73', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.70  thf('74', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('75', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.70  thf('76', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '50', '57'])).
% 0.46/0.70  thf('77', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['75', '76'])).
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
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('91', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['89', '90'])).
% 0.46/0.70  thf('92', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '50', '57'])).
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
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('105', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('106', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.46/0.70  thf('107', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '50', '57'])).
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
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['68', '110'])).
% 0.46/0.70  thf('112', plain,
% 0.46/0.70      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70           sk_C)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['1', '111'])).
% 0.46/0.70  thf('113', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('114', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('115', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.46/0.70  thf('116', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.70  thf(t31_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.70           ( m1_subset_1 @
% 0.46/0.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('117', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (m1_subset_1 @ (k2_funct_1 @ X20) @ 
% 0.46/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('118', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['116', '117'])).
% 0.46/0.70  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('120', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.70  thf('121', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.70  thf('122', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('123', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 0.46/0.70  thf('124', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['123'])).
% 0.46/0.70  thf('125', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.46/0.70          | ~ (v2_funct_1 @ X27)
% 0.46/0.70          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.46/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.46/0.70          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.46/0.70          | ~ (v1_funct_1 @ X27))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.70  thf('126', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70             (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['124', '125'])).
% 0.46/0.70  thf('127', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('128', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf('129', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '50', '57'])).
% 0.46/0.70  thf('130', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['128', '129'])).
% 0.46/0.70  thf('131', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (v1_funct_1 @ (k2_funct_1 @ X20))
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('132', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (u1_struct_0 @ sk_B))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['130', '131'])).
% 0.46/0.70  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('134', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.70  thf('135', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '50', '57'])).
% 0.46/0.70  thf('136', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['134', '135'])).
% 0.46/0.70  thf('137', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf('138', plain,
% 0.46/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.46/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('139', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['137', '138'])).
% 0.46/0.70  thf('140', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '50', '57'])).
% 0.46/0.70  thf('141', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['139', '140'])).
% 0.46/0.70  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('143', plain,
% 0.46/0.70      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['132', '133', '136', '141', '142'])).
% 0.46/0.70  thf('144', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['127', '143'])).
% 0.46/0.70  thf('145', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('147', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.46/0.70  thf('148', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.70  thf('149', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.70  thf('150', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X20)
% 0.46/0.70          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.46/0.70          | (v1_funct_2 @ (k2_funct_1 @ X20) @ X21 @ X22)
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.46/0.70          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.46/0.70          | ~ (v1_funct_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('151', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70           (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['149', '150'])).
% 0.46/0.70  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('153', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.70  thf('154', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.70  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('156', plain,
% 0.46/0.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70         (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['151', '152', '153', '154', '155'])).
% 0.46/0.70  thf('157', plain,
% 0.46/0.70      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70        (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['156'])).
% 0.46/0.70  thf('158', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['126', '148', '157'])).
% 0.46/0.70  thf('159', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['123'])).
% 0.46/0.70  thf('160', plain,
% 0.46/0.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.46/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('161', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['159', '160'])).
% 0.46/0.70  thf('162', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['158', '161'])).
% 0.46/0.70  thf('163', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.70  thf('164', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.70  thf('165', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('166', plain,
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
% 0.46/0.70  thf('167', plain,
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
% 0.46/0.70  thf('168', plain,
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
% 0.46/0.70      inference('sup-', [status(thm)], ['166', '167'])).
% 0.46/0.70  thf('169', plain,
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
% 0.46/0.70      inference('simplify', [status(thm)], ['168'])).
% 0.46/0.70  thf('170', plain,
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
% 0.46/0.70      inference('sup-', [status(thm)], ['165', '169'])).
% 0.46/0.70  thf('171', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('172', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('173', plain,
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
% 0.46/0.70      inference('demod', [status(thm)], ['170', '171', '172'])).
% 0.46/0.70  thf('174', plain,
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
% 0.46/0.70      inference('sup-', [status(thm)], ['164', '173'])).
% 0.46/0.70  thf('175', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.70  thf('176', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.70  thf('177', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['61', '62', '65'])).
% 0.46/0.70  thf('178', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('179', plain,
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
% 0.46/0.70      inference('demod', [status(thm)], ['174', '175', '176', '177', '178'])).
% 0.46/0.70  thf('180', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | (v2_funct_1 @ 
% 0.46/0.70           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['163', '179'])).
% 0.46/0.70  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('182', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['134', '135'])).
% 0.46/0.70  thf('183', plain,
% 0.46/0.70      (![X23 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('184', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['128', '129'])).
% 0.46/0.70  thf('185', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.46/0.70          | ~ (v2_funct_1 @ X27)
% 0.46/0.70          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.46/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.46/0.70          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.46/0.70          | ~ (v1_funct_1 @ X27))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.70  thf('186', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['184', '185'])).
% 0.46/0.70  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('188', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['134', '135'])).
% 0.46/0.70  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('190', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['139', '140'])).
% 0.46/0.70  thf('191', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70          = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['186', '187', '188', '189', '190'])).
% 0.46/0.70  thf('192', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['183', '191'])).
% 0.46/0.70  thf('193', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('194', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('195', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['192', '193', '194'])).
% 0.46/0.70  thf('196', plain,
% 0.46/0.70      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['195'])).
% 0.46/0.70  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('198', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['139', '140'])).
% 0.46/0.70  thf('199', plain,
% 0.46/0.70      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)],
% 0.46/0.70                ['180', '181', '182', '196', '197', '198'])).
% 0.46/0.70  thf('200', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['199'])).
% 0.46/0.70  thf('201', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['162', '200'])).
% 0.46/0.70  thf(t55_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.70       ( ( v2_funct_1 @ A ) =>
% 0.46/0.70         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.70           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('202', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X0)
% 0.46/0.70          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('203', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X0)
% 0.46/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('204', plain,
% 0.46/0.70      (![X1 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('205', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['199'])).
% 0.46/0.70  thf('206', plain,
% 0.46/0.70      (![X1 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('207', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X0)
% 0.46/0.70          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('208', plain,
% 0.46/0.70      (![X1 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('209', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X0)
% 0.46/0.70          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('210', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         (((k1_relat_1 @ X15) != (X14))
% 0.46/0.70          | (v1_partfun1 @ X15 @ X14)
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ X14)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('211', plain,
% 0.46/0.70      (![X15 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X15)
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ (k1_relat_1 @ X15))
% 0.46/0.70          | (v1_partfun1 @ X15 @ (k1_relat_1 @ X15)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['210'])).
% 0.46/0.70  thf('212', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['209', '211'])).
% 0.46/0.70  thf('213', plain,
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
% 0.46/0.70      inference('sup-', [status(thm)], ['208', '212'])).
% 0.46/0.70  thf('214', plain,
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
% 0.46/0.70      inference('sup-', [status(thm)], ['207', '213'])).
% 0.46/0.70  thf('215', plain,
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
% 0.46/0.70      inference('simplify', [status(thm)], ['214'])).
% 0.46/0.70  thf('216', plain,
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
% 0.46/0.70      inference('sup-', [status(thm)], ['206', '215'])).
% 0.46/0.70  thf('217', plain,
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
% 0.46/0.70      inference('simplify', [status(thm)], ['216'])).
% 0.46/0.70  thf('218', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['205', '217'])).
% 0.46/0.70  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('221', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('222', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('223', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '50', '57'])).
% 0.46/0.70  thf('224', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['222', '223'])).
% 0.46/0.70  thf('225', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['123'])).
% 0.46/0.70  thf('226', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X2)
% 0.46/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('227', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['225', '226'])).
% 0.46/0.70  thf('228', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.70  thf('229', plain,
% 0.46/0.70      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)],
% 0.46/0.70                ['218', '219', '220', '221', '224', '227', '228'])).
% 0.46/0.70  thf('230', plain,
% 0.46/0.70      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['204', '229'])).
% 0.46/0.70  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('234', plain,
% 0.46/0.70      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['230', '231', '232', '233'])).
% 0.46/0.70  thf('235', plain,
% 0.46/0.70      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['203', '234'])).
% 0.46/0.70  thf('236', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['225', '226'])).
% 0.46/0.70  thf('237', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.70  thf('238', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['199'])).
% 0.46/0.70  thf('239', plain,
% 0.46/0.70      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['235', '236', '237', '238'])).
% 0.46/0.70  thf('240', plain,
% 0.46/0.70      (![X14 : $i, X15 : $i]:
% 0.46/0.70         (~ (v1_partfun1 @ X15 @ X14)
% 0.46/0.70          | ((k1_relat_1 @ X15) = (X14))
% 0.46/0.70          | ~ (v4_relat_1 @ X15 @ X14)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('241', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['239', '240'])).
% 0.46/0.70  thf('242', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('243', plain,
% 0.46/0.70      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['241', '242'])).
% 0.46/0.70  thf('244', plain,
% 0.46/0.70      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['202', '243'])).
% 0.46/0.70  thf('245', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['222', '223'])).
% 0.46/0.70  thf('246', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('247', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('248', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('249', plain,
% 0.46/0.70      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['244', '245', '246', '247', '248'])).
% 0.46/0.70  thf('250', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['201', '249'])).
% 0.46/0.70  thf('251', plain,
% 0.46/0.70      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['250'])).
% 0.46/0.70  thf('252', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['115', '251'])).
% 0.46/0.70  thf('253', plain,
% 0.46/0.70      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.70           sk_C)
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['0', '252'])).
% 0.46/0.70  thf('254', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['128', '129'])).
% 0.46/0.70  thf('255', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['128', '129'])).
% 0.46/0.70  thf(reflexivity_r2_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.70         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.46/0.70  thf('256', plain,
% 0.46/0.70      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.70         ((r2_funct_2 @ X16 @ X17 @ X18 @ X18)
% 0.46/0.70          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.46/0.70          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.46/0.70          | ~ (v1_funct_1 @ X18)
% 0.46/0.70          | ~ (v1_funct_1 @ X19)
% 0.46/0.70          | ~ (v1_funct_2 @ X19 @ X16 @ X17)
% 0.46/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.70      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.46/0.70  thf('257', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.70             sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['255', '256'])).
% 0.46/0.70  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('259', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['134', '135'])).
% 0.46/0.70  thf('260', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.70             sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['257', '258', '259'])).
% 0.46/0.70  thf('261', plain,
% 0.46/0.70      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['254', '260'])).
% 0.46/0.70  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('263', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['134', '135'])).
% 0.46/0.70  thf('264', plain,
% 0.46/0.70      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['261', '262', '263'])).
% 0.46/0.70  thf('265', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('266', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('267', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('268', plain, ($false),
% 0.46/0.70      inference('demod', [status(thm)], ['253', '264', '265', '266', '267'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
