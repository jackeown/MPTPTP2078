%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGN5b7eVuo

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:20 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  298 (7456 expanded)
%              Number of leaves         :   39 (2163 expanded)
%              Depth                    :   35
%              Number of atoms          : 2847 (161203 expanded)
%              Number of equality atoms :  138 (4445 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','36'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('53',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','48','49','50','51','52'])).

thf('54',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    inference('sup+',[status(thm)],['26','27'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','36'])).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('74',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
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
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    inference('sup+',[status(thm)],['26','27'])).

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
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    inference('sup+',[status(thm)],['26','27'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    inference(demod,[status(thm)],['39','44','47'])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('149',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_struct_0 @ X29 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 )
       != ( k2_struct_0 @ X29 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_struct_0 @ X30 ) ) ),
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
    inference('sup+',[status(thm)],['26','27'])).

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
    inference(demod,[status(thm)],['39','44','47'])).

thf('159',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('160',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

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
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    inference('sup+',[status(thm)],['26','27'])).

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

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('193',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('194',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('195',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('196',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('197',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('198',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('199',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('200',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('201',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != X15 )
      | ( v1_partfun1 @ X16 @ X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('202',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v4_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
      | ( v1_partfun1 @ X16 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['200','202'])).

thf('204',plain,(
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
    inference('sup-',[status(thm)],['199','203'])).

thf('205',plain,(
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
    inference('sup-',[status(thm)],['198','204'])).

thf('206',plain,(
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
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
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
    inference('sup-',[status(thm)],['197','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['196','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('214',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('215',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('218',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('220',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('222',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['209','210','211','212','215','220','221'])).

thf('223',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['195','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['223','224','225','226'])).

thf('228',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['194','227'])).

thf('229',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('230',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('231',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('232',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['228','229','230','231'])).

thf('233',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('234',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('236',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['193','236'])).

thf('238',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('239',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('240',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['237','238','239','240','241'])).

thf('243',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['192','242'])).

thf('244',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['111','244'])).

thf('246',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','245'])).

thf('247',plain,(
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

thf('248',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_funct_2 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('249',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_funct_2 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['247','249'])).

thf('251',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('252',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('255',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    $false ),
    inference(demod,[status(thm)],['246','253','254','255','256'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGN5b7eVuo
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 449 iterations in 0.202s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.67  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.67  thf(t65_funct_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.67       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (![X5 : $i]:
% 0.45/0.67         (~ (v2_funct_1 @ X5)
% 0.45/0.67          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.45/0.67          | ~ (v1_funct_1 @ X5)
% 0.45/0.67          | ~ (v1_relat_1 @ X5))),
% 0.45/0.67      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.67  thf(d3_struct_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf(t64_tops_2, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_struct_0 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ( ( ( k2_relset_1 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.67                 ( r2_funct_2 @
% 0.45/0.67                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.67                   ( k2_tops_2 @
% 0.45/0.67                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                     ( k2_tops_2 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.67                   C ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( l1_struct_0 @ A ) =>
% 0.45/0.67          ( ![B:$i]:
% 0.45/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.67              ( ![C:$i]:
% 0.45/0.67                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                    ( v1_funct_2 @
% 0.45/0.67                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                    ( m1_subset_1 @
% 0.45/0.67                      C @ 
% 0.45/0.67                      ( k1_zfmisc_1 @
% 0.45/0.67                        ( k2_zfmisc_1 @
% 0.45/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67                  ( ( ( ( k2_relset_1 @
% 0.45/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                        ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                      ( v2_funct_1 @ C ) ) =>
% 0.45/0.67                    ( r2_funct_2 @
% 0.45/0.67                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.67                      ( k2_tops_2 @
% 0.45/0.67                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                        ( k2_tops_2 @
% 0.45/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.67                      C ) ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67           sk_C)
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.67  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67           sk_C)
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '6'])).
% 0.45/0.67  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (((m1_subset_1 @ sk_C @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.67  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf(cc5_funct_2, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.67       ( ![C:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.67             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.45/0.67          | (v1_partfun1 @ X12 @ X13)
% 0.45/0.67          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.45/0.67          | ~ (v1_funct_1 @ X12)
% 0.45/0.67          | (v1_xboole_0 @ X14))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.67        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.67  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.45/0.67        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['16', '17', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.67         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.67          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['23', '28'])).
% 0.45/0.67  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf(fc5_struct_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.67       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X25 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ (k2_struct_0 @ X25))
% 0.45/0.67          | ~ (l1_struct_0 @ X25)
% 0.45/0.67          | (v2_struct_0 @ X25))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | (v2_struct_0 @ sk_B)
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.67  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['32', '33'])).
% 0.45/0.67  thf('35', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('36', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('clc', [status(thm)], ['34', '35'])).
% 0.45/0.67  thf('37', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['29', '36'])).
% 0.45/0.67  thf(d4_partfun1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.67       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (![X15 : $i, X16 : $i]:
% 0.45/0.67         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.67          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.67          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.67          | ~ (v1_relat_1 @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.67        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.67        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(cc2_relat_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.67          | (v1_relat_1 @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ 
% 0.45/0.67           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | (v1_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.67  thf(fc6_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.67  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(cc2_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.67         ((v4_relat_1 @ X6 @ X7)
% 0.45/0.67          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.67  thf('47', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.67  thf('48', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.45/0.67  thf('49', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('50', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.45/0.67  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.45/0.67  thf('52', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '48', '49', '50', '51', '52'])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (((m1_subset_1 @ sk_C @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['55', '56'])).
% 0.45/0.67  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('59', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (((m1_subset_1 @ sk_C @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['54', '59'])).
% 0.45/0.67  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.67  thf('63', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('64', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.67      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.67  thf('65', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('66', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['29', '36'])).
% 0.45/0.67  thf('67', plain,
% 0.45/0.67      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.67  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('69', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.67  thf('70', plain,
% 0.45/0.67      (![X15 : $i, X16 : $i]:
% 0.45/0.67         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.67          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.67          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.67          | ~ (v1_relat_1 @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.67  thf('71', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.67        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.67        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.67  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.67  thf('73', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.67  thf('74', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.67         ((v4_relat_1 @ X6 @ X7)
% 0.45/0.67          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.67  thf('75', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.67  thf('76', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.45/0.67  thf('77', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.67      inference('demod', [status(thm)], ['64', '76'])).
% 0.45/0.67  thf(d4_tops_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.67       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.67         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.67  thf('78', plain,
% 0.45/0.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.67         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.67          | ~ (v2_funct_1 @ X28)
% 0.45/0.67          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.67          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.67          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.67          | ~ (v1_funct_1 @ X28))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.67  thf('79', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67            = (k2_funct_1 @ sk_C))
% 0.45/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.67        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67            != (k2_relat_1 @ sk_C)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.67  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('81', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('82', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('83', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('84', plain,
% 0.45/0.67      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['82', '83'])).
% 0.45/0.67  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('86', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.67  thf('87', plain,
% 0.45/0.67      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['81', '86'])).
% 0.45/0.67  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('89', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['87', '88'])).
% 0.45/0.67  thf('90', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('91', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.67  thf('92', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.45/0.67  thf('93', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.67  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('95', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('96', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('97', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('98', plain,
% 0.45/0.67      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67          = (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['96', '97'])).
% 0.45/0.67  thf('99', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('100', plain,
% 0.45/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['98', '99'])).
% 0.45/0.67  thf('101', plain,
% 0.45/0.67      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67          = (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['95', '100'])).
% 0.45/0.67  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('103', plain,
% 0.45/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['101', '102'])).
% 0.45/0.67  thf('104', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('105', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('106', plain,
% 0.45/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67         = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.45/0.67  thf('107', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.45/0.67  thf('108', plain,
% 0.45/0.67      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67         = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['106', '107'])).
% 0.45/0.67  thf('109', plain,
% 0.45/0.67      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67          = (k2_funct_1 @ sk_C))
% 0.45/0.67        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['79', '80', '93', '94', '108'])).
% 0.45/0.67  thf('110', plain,
% 0.45/0.67      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67         = (k2_funct_1 @ sk_C))),
% 0.45/0.67      inference('simplify', [status(thm)], ['109'])).
% 0.45/0.67  thf('111', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['53', '110'])).
% 0.45/0.67  thf('112', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.67      inference('demod', [status(thm)], ['64', '76'])).
% 0.45/0.67  thf(t31_funct_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.67       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.67         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.67           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.67           ( m1_subset_1 @
% 0.45/0.67             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.67  thf('113', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.67         (~ (v2_funct_1 @ X21)
% 0.45/0.67          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.67          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.45/0.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.67          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.67          | ~ (v1_funct_1 @ X21))),
% 0.45/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.67  thf('114', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.45/0.67        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67            != (k2_relat_1 @ sk_C))
% 0.45/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['112', '113'])).
% 0.45/0.67  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('116', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.67  thf('117', plain,
% 0.45/0.67      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67         = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['106', '107'])).
% 0.45/0.67  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('119', plain,
% 0.45/0.67      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.45/0.67        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 0.45/0.67  thf('120', plain,
% 0.45/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.67      inference('simplify', [status(thm)], ['119'])).
% 0.45/0.67  thf('121', plain,
% 0.45/0.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.67         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.67          | ~ (v2_funct_1 @ X28)
% 0.45/0.67          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.67          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.67          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.67          | ~ (v1_funct_1 @ X28))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.67  thf('122', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.67        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.67             (k1_relat_1 @ sk_C))
% 0.45/0.67        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.67        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.67        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['120', '121'])).
% 0.45/0.67  thf('123', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.67      inference('demod', [status(thm)], ['64', '76'])).
% 0.45/0.67  thf('124', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.67         (~ (v2_funct_1 @ X21)
% 0.45/0.67          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.67          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.67          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.67          | ~ (v1_funct_1 @ X21))),
% 0.45/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.67  thf('125', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.67        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67            != (k2_relat_1 @ sk_C))
% 0.45/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['123', '124'])).
% 0.45/0.67  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('127', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.67  thf('128', plain,
% 0.45/0.67      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67         = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['106', '107'])).
% 0.45/0.67  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('130', plain,
% 0.45/0.67      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.67        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 0.45/0.67  thf('131', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.67      inference('simplify', [status(thm)], ['130'])).
% 0.45/0.67  thf('132', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.67      inference('demod', [status(thm)], ['64', '76'])).
% 0.45/0.67  thf('133', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.67         (~ (v2_funct_1 @ X21)
% 0.45/0.67          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.67          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.67          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.67          | ~ (v1_funct_1 @ X21))),
% 0.45/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.67  thf('134', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.67           (k1_relat_1 @ sk_C))
% 0.45/0.67        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67            != (k2_relat_1 @ sk_C))
% 0.45/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['132', '133'])).
% 0.45/0.67  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('136', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.67  thf('137', plain,
% 0.45/0.67      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67         = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['106', '107'])).
% 0.45/0.67  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('139', plain,
% 0.45/0.67      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.67         (k1_relat_1 @ sk_C))
% 0.45/0.67        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 0.45/0.67  thf('140', plain,
% 0.45/0.67      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.67        (k1_relat_1 @ sk_C))),
% 0.45/0.67      inference('simplify', [status(thm)], ['139'])).
% 0.45/0.67  thf('141', plain,
% 0.45/0.67      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.67        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.67        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['122', '131', '140'])).
% 0.45/0.67  thf('142', plain,
% 0.45/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.67      inference('simplify', [status(thm)], ['119'])).
% 0.45/0.67  thf('143', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.67         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.67          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.67  thf('144', plain,
% 0.45/0.67      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['142', '143'])).
% 0.45/0.68  thf('145', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['141', '144'])).
% 0.45/0.68  thf('146', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['64', '76'])).
% 0.45/0.68  thf('147', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.45/0.68  thf('148', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf('149', plain,
% 0.45/0.68      (![X24 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf(t63_tops_2, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_struct_0 @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( l1_struct_0 @ B ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.68                 ( m1_subset_1 @
% 0.45/0.68                   C @ 
% 0.45/0.68                   ( k1_zfmisc_1 @
% 0.45/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.68               ( ( ( ( k2_relset_1 @
% 0.45/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.68                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.68                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.68                 ( v2_funct_1 @
% 0.45/0.68                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('150', plain,
% 0.45/0.68      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.68         (~ (l1_struct_0 @ X29)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31)
% 0.45/0.68              != (k2_struct_0 @ X29))
% 0.45/0.68          | ~ (v2_funct_1 @ X31)
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31))
% 0.45/0.68          | ~ (m1_subset_1 @ X31 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.45/0.68          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.45/0.68          | ~ (v1_funct_1 @ X31)
% 0.45/0.68          | ~ (l1_struct_0 @ X30))),
% 0.45/0.68      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.45/0.68  thf('151', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X2 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.45/0.68          | ~ (l1_struct_0 @ X0)
% 0.45/0.68          | ~ (l1_struct_0 @ X1)
% 0.45/0.68          | ~ (v1_funct_1 @ X2)
% 0.45/0.68          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.45/0.68          | ~ (v2_funct_1 @ X2)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.45/0.68              != (k2_struct_0 @ X0))
% 0.45/0.68          | ~ (l1_struct_0 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['149', '150'])).
% 0.45/0.68  thf('152', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.45/0.68            != (k2_struct_0 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ X2)
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.45/0.68          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ X2)
% 0.45/0.68          | ~ (l1_struct_0 @ X1)
% 0.45/0.68          | ~ (l1_struct_0 @ X0)
% 0.45/0.68          | ~ (m1_subset_1 @ X2 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['151'])).
% 0.45/0.68  thf('153', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.45/0.68          | ~ (l1_struct_0 @ sk_B)
% 0.45/0.68          | ~ (l1_struct_0 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X1)
% 0.45/0.68          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.45/0.68          | ~ (v2_funct_1 @ X1)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.45/0.68              != (k2_struct_0 @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['148', '152'])).
% 0.45/0.68  thf('154', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('155', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf('156', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.45/0.68          | ~ (l1_struct_0 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X1)
% 0.45/0.68          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.45/0.68          | ~ (v2_funct_1 @ X1)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.45/0.68              != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.45/0.68  thf('157', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0)
% 0.45/0.68              != (k2_relat_1 @ sk_C))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0))
% 0.45/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['147', '156'])).
% 0.45/0.68  thf('158', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.45/0.68  thf('159', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.45/0.68  thf('160', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.45/0.68  thf('161', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('162', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.45/0.68          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0)
% 0.45/0.68              != (k2_relat_1 @ sk_C))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0))
% 0.45/0.68          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | ~ (v1_funct_1 @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 0.45/0.68  thf('163', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | (v2_funct_1 @ 
% 0.45/0.68           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['146', '162'])).
% 0.45/0.68  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('165', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.68  thf('166', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.45/0.68  thf('167', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['165', '166'])).
% 0.45/0.68  thf('168', plain,
% 0.45/0.68      (![X24 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('169', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.68  thf('170', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.45/0.68  thf('171', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['169', '170'])).
% 0.45/0.68  thf('172', plain,
% 0.45/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.68          | ~ (v2_funct_1 @ X28)
% 0.45/0.68          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.68          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.68          | ~ (v1_funct_1 @ X28))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.68  thf('173', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['171', '172'])).
% 0.45/0.68  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('175', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['165', '166'])).
% 0.45/0.68  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('177', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.68  thf('178', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.68          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('179', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['177', '178'])).
% 0.45/0.68  thf('180', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.45/0.68  thf('181', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['179', '180'])).
% 0.45/0.68  thf('182', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68          = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['173', '174', '175', '176', '181'])).
% 0.45/0.68  thf('183', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.68        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['168', '182'])).
% 0.45/0.68  thf('184', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf('185', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('186', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.45/0.68  thf('187', plain,
% 0.45/0.68      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['186'])).
% 0.45/0.68  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('189', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['179', '180'])).
% 0.45/0.68  thf('190', plain,
% 0.45/0.68      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['163', '164', '167', '187', '188', '189'])).
% 0.45/0.68  thf('191', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['190'])).
% 0.45/0.68  thf('192', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['145', '191'])).
% 0.45/0.68  thf(t55_funct_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.68       ( ( v2_funct_1 @ A ) =>
% 0.45/0.68         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.68           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('193', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('194', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('195', plain,
% 0.45/0.68      (![X5 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X5)
% 0.45/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.45/0.68          | ~ (v1_funct_1 @ X5)
% 0.45/0.68          | ~ (v1_relat_1 @ X5))),
% 0.45/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.68  thf('196', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['190'])).
% 0.45/0.68  thf('197', plain,
% 0.45/0.68      (![X5 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X5)
% 0.45/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.45/0.68          | ~ (v1_funct_1 @ X5)
% 0.45/0.68          | ~ (v1_relat_1 @ X5))),
% 0.45/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.68  thf('198', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('199', plain,
% 0.45/0.68      (![X5 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X5)
% 0.45/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.45/0.68          | ~ (v1_funct_1 @ X5)
% 0.45/0.68          | ~ (v1_relat_1 @ X5))),
% 0.45/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.68  thf('200', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('201', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i]:
% 0.45/0.68         (((k1_relat_1 @ X16) != (X15))
% 0.45/0.68          | (v1_partfun1 @ X16 @ X15)
% 0.45/0.68          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.68          | ~ (v1_relat_1 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.68  thf('202', plain,
% 0.45/0.68      (![X16 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ X16)
% 0.45/0.68          | ~ (v4_relat_1 @ X16 @ (k1_relat_1 @ X16))
% 0.45/0.68          | (v1_partfun1 @ X16 @ (k1_relat_1 @ X16)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['201'])).
% 0.45/0.68  thf('203', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['200', '202'])).
% 0.45/0.68  thf('204', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['199', '203'])).
% 0.45/0.68  thf('205', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['198', '204'])).
% 0.45/0.68  thf('206', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['205'])).
% 0.45/0.68  thf('207', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['197', '206'])).
% 0.45/0.68  thf('208', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0))),
% 0.45/0.68      inference('simplify', [status(thm)], ['207'])).
% 0.45/0.68  thf('209', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['196', '208'])).
% 0.45/0.68  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('213', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.68  thf('214', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.45/0.68  thf('215', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['213', '214'])).
% 0.45/0.68  thf('216', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['119'])).
% 0.45/0.68  thf('217', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.68          | (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.68  thf('218', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ 
% 0.45/0.68           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.45/0.68        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['216', '217'])).
% 0.45/0.68  thf('219', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.68  thf('220', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['218', '219'])).
% 0.45/0.68  thf('221', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['130'])).
% 0.45/0.68  thf('222', plain,
% 0.45/0.68      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['209', '210', '211', '212', '215', '220', '221'])).
% 0.45/0.68  thf('223', plain,
% 0.45/0.68      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup+', [status(thm)], ['195', '222'])).
% 0.45/0.68  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('226', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('227', plain,
% 0.45/0.68      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['223', '224', '225', '226'])).
% 0.45/0.68  thf('228', plain,
% 0.45/0.68      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['194', '227'])).
% 0.45/0.68  thf('229', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['218', '219'])).
% 0.45/0.68  thf('230', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['130'])).
% 0.45/0.68  thf('231', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['190'])).
% 0.45/0.68  thf('232', plain,
% 0.45/0.68      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['228', '229', '230', '231'])).
% 0.45/0.68  thf('233', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i]:
% 0.45/0.68         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.68          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.68          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.68          | ~ (v1_relat_1 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.68  thf('234', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['232', '233'])).
% 0.45/0.68  thf('235', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('236', plain,
% 0.45/0.68      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['234', '235'])).
% 0.45/0.68  thf('237', plain,
% 0.45/0.68      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['193', '236'])).
% 0.45/0.68  thf('238', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['213', '214'])).
% 0.45/0.68  thf('239', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('240', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('241', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('242', plain,
% 0.45/0.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['237', '238', '239', '240', '241'])).
% 0.45/0.68  thf('243', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['192', '242'])).
% 0.45/0.68  thf('244', plain,
% 0.45/0.68      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['243'])).
% 0.45/0.68  thf('245', plain,
% 0.45/0.68      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['111', '244'])).
% 0.45/0.68  thf('246', plain,
% 0.45/0.68      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68           sk_C)
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['0', '245'])).
% 0.45/0.68  thf('247', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['169', '170'])).
% 0.45/0.68  thf(redefinition_r2_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.68         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.45/0.68  thf('248', plain,
% 0.45/0.68      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.68          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.45/0.68          | ~ (v1_funct_1 @ X17)
% 0.45/0.68          | ~ (v1_funct_1 @ X20)
% 0.45/0.68          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.45/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.68          | (r2_funct_2 @ X18 @ X19 @ X17 @ X20)
% 0.45/0.68          | ((X17) != (X20)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.45/0.68  thf('249', plain,
% 0.45/0.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.68         ((r2_funct_2 @ X18 @ X19 @ X20 @ X20)
% 0.45/0.68          | ~ (v1_funct_1 @ X20)
% 0.45/0.68          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.45/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['248'])).
% 0.45/0.68  thf('250', plain,
% 0.45/0.68      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68           sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['247', '249'])).
% 0.45/0.68  thf('251', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['165', '166'])).
% 0.45/0.68  thf('252', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('253', plain,
% 0.45/0.68      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['250', '251', '252'])).
% 0.45/0.68  thf('254', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('255', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('256', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('257', plain, ($false),
% 0.45/0.68      inference('demod', [status(thm)], ['246', '253', '254', '255', '256'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
