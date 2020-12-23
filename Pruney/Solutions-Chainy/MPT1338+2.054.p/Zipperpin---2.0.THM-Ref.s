%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zc5z4htaF1

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:56 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 603 expanded)
%              Number of leaves         :   46 ( 193 expanded)
%              Depth                    :   23
%              Number of atoms          : 1975 (15982 expanded)
%              Number of equality atoms :  159 ( 902 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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
    inference('sup+',[status(thm)],['2','3'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( ( k5_relat_1 @ X24 @ ( k2_funct_1 @ X24 ) )
        = ( k6_partfun1 @ X25 ) )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X25 @ X23 @ X24 )
       != X23 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k6_partfun1 @ X17 )
      = ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( ( k5_relat_1 @ X24 @ ( k2_funct_1 @ X24 ) )
        = ( k6_relat_1 @ X25 ) )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X25 @ X23 @ X24 )
       != X23 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('33',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','33','34','41','42'])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('46',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('47',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k1_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('53',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('55',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t171_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relset_1 @ X19 @ X19 @ ( k6_partfun1 @ X19 ) @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t171_funct_2])).

thf('57',plain,(
    ! [X17: $i] :
      ( ( k6_partfun1 @ X17 )
      = ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relset_1 @ X19 @ X19 @ ( k6_relat_1 @ X19 ) @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('63',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','61','64','65','66'])).

thf('68',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('72',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('79',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('87',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','92'])).

thf('94',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

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

thf('96',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('100',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('105',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('108',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('114',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('117',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['73'])).

thf('119',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('124',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','124'])).

thf('126',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','125'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('128',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','129'])).

thf('131',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['73'])).

thf('138',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['136','137'])).

thf('139',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['93','138'])).

thf('140',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('141',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('142',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','142'])).

thf('144',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','148'])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['149'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('151',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('152',plain,(
    $false ),
    inference(demod,[status(thm)],['13','150','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zc5z4htaF1
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 475 iterations in 0.148s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.41/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.60  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.41/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.60  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.41/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.60  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(t62_tops_2, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_struct_0 @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                 ( m1_subset_1 @
% 0.41/0.60                   C @ 
% 0.41/0.60                   ( k1_zfmisc_1 @
% 0.41/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60               ( ( ( ( k2_relset_1 @
% 0.41/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.41/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.41/0.60                   ( v2_funct_1 @ C ) ) =>
% 0.41/0.60                 ( ( ( k1_relset_1 @
% 0.41/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.60                       ( k2_tops_2 @
% 0.41/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.41/0.60                   ( ( k2_relset_1 @
% 0.41/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.60                       ( k2_tops_2 @
% 0.41/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.60                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( l1_struct_0 @ A ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.41/0.60              ( ![C:$i]:
% 0.41/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60                    ( v1_funct_2 @
% 0.41/0.60                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                    ( m1_subset_1 @
% 0.41/0.60                      C @ 
% 0.41/0.60                      ( k1_zfmisc_1 @
% 0.41/0.60                        ( k2_zfmisc_1 @
% 0.41/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                  ( ( ( ( k2_relset_1 @
% 0.41/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.41/0.60                        ( k2_struct_0 @ B ) ) & 
% 0.41/0.60                      ( v2_funct_1 @ C ) ) =>
% 0.41/0.60                    ( ( ( k1_relset_1 @
% 0.41/0.60                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.60                          ( k2_tops_2 @
% 0.41/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.60                        ( k2_struct_0 @ B ) ) & 
% 0.41/0.60                      ( ( k2_relset_1 @
% 0.41/0.60                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.60                          ( k2_tops_2 @
% 0.41/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.60                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.60         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.41/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60         = (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60         = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf(d3_struct_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X26 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf(fc2_struct_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.60       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X27 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ (u1_struct_0 @ X27))
% 0.41/0.60          | ~ (l1_struct_0 @ X27)
% 0.41/0.60          | (v2_struct_0 @ X27))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | (v2_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['7'])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.41/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.41/0.60        | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '8'])).
% 0.41/0.60  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('13', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('clc', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X26 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X26 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (((m1_subset_1 @ sk_C @ 
% 0.41/0.60         (k1_zfmisc_1 @ 
% 0.41/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.41/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.60  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf('20', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.41/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf(t35_funct_2, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.41/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.60           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.41/0.60             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.60         (((X23) = (k1_xboole_0))
% 0.41/0.60          | ~ (v1_funct_1 @ X24)
% 0.41/0.60          | ~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.41/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.41/0.60          | ((k5_relat_1 @ X24 @ (k2_funct_1 @ X24)) = (k6_partfun1 @ X25))
% 0.41/0.60          | ~ (v2_funct_1 @ X24)
% 0.41/0.60          | ((k2_relset_1 @ X25 @ X23 @ X24) != (X23)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.41/0.60  thf(redefinition_k6_partfun1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.41/0.60  thf('23', plain, (![X17 : $i]: ((k6_partfun1 @ X17) = (k6_relat_1 @ X17))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.60         (((X23) = (k1_xboole_0))
% 0.41/0.60          | ~ (v1_funct_1 @ X24)
% 0.41/0.60          | ~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.41/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.41/0.60          | ((k5_relat_1 @ X24 @ (k2_funct_1 @ X24)) = (k6_relat_1 @ X25))
% 0.41/0.60          | ~ (v2_funct_1 @ X24)
% 0.41/0.60          | ((k2_relset_1 @ X25 @ X23 @ X24) != (X23)))),
% 0.41/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60          != (k2_relat_1 @ sk_C))
% 0.41/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.60        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.60            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.41/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.60        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '24'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X26 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60         = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60          = (k2_struct_0 @ sk_B))
% 0.41/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.41/0.60  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60         = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60         = (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.41/0.60  thf('34', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X26 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.41/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['37', '38'])).
% 0.41/0.60  thf('40', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.41/0.60        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.60            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['25', '33', '34', '41', '42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.41/0.60        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.60            = (k6_relat_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.60  thf(t58_funct_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60       ( ( v2_funct_1 @ A ) =>
% 0.41/0.60         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.41/0.60             ( k1_relat_1 @ A ) ) & 
% 0.41/0.60           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.41/0.60             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X3 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X3)
% 0.41/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ (k2_funct_1 @ X3)))
% 0.41/0.60              = (k1_relat_1 @ X3))
% 0.41/0.60          | ~ (v1_funct_1 @ X3)
% 0.41/0.60          | ~ (v1_relat_1 @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      ((((k1_relat_1 @ (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          = (k1_relat_1 @ sk_C))
% 0.41/0.60        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.60      inference('sup+', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf(t29_relset_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( m1_subset_1 @
% 0.41/0.60       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X13 : $i]:
% 0.41/0.60         (m1_subset_1 @ (k6_relat_1 @ X13) @ 
% 0.41/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.41/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.60         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.41/0.60          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k1_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 0.41/0.60           = (k1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X13 : $i]:
% 0.41/0.60         (m1_subset_1 @ (k6_relat_1 @ X13) @ 
% 0.41/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.41/0.60  thf(t38_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.41/0.60         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.60         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 0.41/0.60            = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.41/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.41/0.60      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k8_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X0)
% 0.41/0.60           = (k1_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.60  thf(dt_k2_subset_1, axiom,
% 0.41/0.60    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.41/0.60  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.41/0.60  thf('54', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.60  thf('55', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.41/0.60      inference('demod', [status(thm)], ['53', '54'])).
% 0.41/0.60  thf(t171_funct_2, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         (((k8_relset_1 @ X19 @ X19 @ (k6_partfun1 @ X19) @ X18) = (X18))
% 0.41/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t171_funct_2])).
% 0.41/0.60  thf('57', plain, (![X17 : $i]: ((k6_partfun1 @ X17) = (k6_relat_1 @ X17))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         (((k8_relset_1 @ X19 @ X19 @ (k6_relat_1 @ X19) @ X18) = (X18))
% 0.41/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.41/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      (![X0 : $i]: ((k8_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['55', '58'])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      (![X0 : $i]: ((X0) = (k1_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['52', '59'])).
% 0.41/0.60  thf('61', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['49', '60'])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(cc1_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( v1_relat_1 @ C ) ))).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.60         ((v1_relat_1 @ X4)
% 0.41/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.41/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.60  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.60      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.60  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.41/0.60        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '61', '64', '65', '66'])).
% 0.41/0.60  thf('68', plain,
% 0.41/0.60      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.41/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.60        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['14', '67'])).
% 0.41/0.60  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('70', plain,
% 0.41/0.60      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.41/0.60        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['68', '69'])).
% 0.41/0.60  thf(t55_funct_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60       ( ( v2_funct_1 @ A ) =>
% 0.41/0.60         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.41/0.60           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('71', plain,
% 0.41/0.60      (![X2 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X2)
% 0.41/0.60          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 0.41/0.60          | ~ (v1_funct_1 @ X2)
% 0.41/0.60          | ~ (v1_relat_1 @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.41/0.60  thf('72', plain,
% 0.41/0.60      (![X26 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_B))
% 0.41/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60            != (k2_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_A)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_A))))),
% 0.41/0.60      inference('split', [status(esa)], ['73'])).
% 0.41/0.60  thf('75', plain,
% 0.41/0.60      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60           != (k2_struct_0 @ sk_A))
% 0.41/0.60         | ~ (l1_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['72', '74'])).
% 0.41/0.60  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('77', plain,
% 0.41/0.60      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_A)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.41/0.60  thf('78', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('79', plain,
% 0.41/0.60      (![X26 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('80', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d4_tops_2, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.41/0.60         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.41/0.60  thf('81', plain,
% 0.41/0.60      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.60         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.41/0.60          | ~ (v2_funct_1 @ X30)
% 0.41/0.60          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.41/0.60          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.41/0.60          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.41/0.60          | ~ (v1_funct_1 @ X30))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.41/0.60  thf('82', plain,
% 0.41/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60            = (k2_funct_1 @ sk_C))
% 0.41/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60            != (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.60  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('84', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('86', plain,
% 0.41/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60         = (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('87', plain,
% 0.41/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60          = (k2_funct_1 @ sk_C))
% 0.41/0.60        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.41/0.60  thf('88', plain,
% 0.41/0.60      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.41/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.41/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60            = (k2_funct_1 @ sk_C)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['79', '87'])).
% 0.41/0.60  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('91', plain,
% 0.41/0.60      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.41/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60            = (k2_funct_1 @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.41/0.60  thf('92', plain,
% 0.41/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.60         = (k2_funct_1 @ sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['91'])).
% 0.41/0.60  thf('93', plain,
% 0.41/0.60      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['77', '78', '92'])).
% 0.41/0.60  thf('94', plain,
% 0.41/0.60      (![X2 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X2)
% 0.41/0.60          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.41/0.60          | ~ (v1_funct_1 @ X2)
% 0.41/0.60          | ~ (v1_relat_1 @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.41/0.60  thf('95', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.41/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf(t31_funct_2, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.41/0.60         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.41/0.60           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.41/0.60           ( m1_subset_1 @
% 0.41/0.60             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.41/0.60  thf('96', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.60         (~ (v2_funct_1 @ X20)
% 0.41/0.60          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.41/0.60          | (m1_subset_1 @ (k2_funct_1 @ X20) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.41/0.60          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.41/0.60          | ~ (v1_funct_1 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.41/0.60  thf('97', plain,
% 0.41/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.41/0.60        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.60           (k1_zfmisc_1 @ 
% 0.41/0.60            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.41/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60            != (k2_relat_1 @ sk_C))
% 0.41/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['95', '96'])).
% 0.41/0.60  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('99', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('100', plain,
% 0.41/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60         = (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.41/0.60  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('102', plain,
% 0.41/0.60      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.60         (k1_zfmisc_1 @ 
% 0.41/0.60          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.41/0.60        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.41/0.60  thf('103', plain,
% 0.41/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['102'])).
% 0.41/0.60  thf('104', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.60         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.41/0.60          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.60  thf('105', plain,
% 0.41/0.60      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['103', '104'])).
% 0.41/0.60  thf('106', plain,
% 0.41/0.60      (![X26 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('107', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.41/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('108', plain,
% 0.41/0.60      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.60         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.41/0.60          | ~ (v2_funct_1 @ X30)
% 0.41/0.60          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.41/0.60          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.41/0.60          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.41/0.60          | ~ (v1_funct_1 @ X30))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.41/0.60  thf('109', plain,
% 0.41/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.41/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60            = (k2_funct_1 @ sk_C))
% 0.41/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60            != (k2_relat_1 @ sk_C)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['107', '108'])).
% 0.41/0.60  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('111', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('113', plain,
% 0.41/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60         = (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.41/0.60  thf('114', plain,
% 0.41/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60          = (k2_funct_1 @ sk_C))
% 0.41/0.60        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 0.41/0.60  thf('115', plain,
% 0.41/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.60         = (k2_funct_1 @ sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['114'])).
% 0.41/0.60  thf('116', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('117', plain,
% 0.41/0.60      (![X26 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('118', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('split', [status(esa)], ['73'])).
% 0.41/0.60  thf('119', plain,
% 0.41/0.60      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60           != (k2_struct_0 @ sk_B))
% 0.41/0.60         | ~ (l1_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['117', '118'])).
% 0.41/0.60  thf('120', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('121', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['119', '120'])).
% 0.41/0.60  thf('122', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.41/0.60          != (k2_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['116', '121'])).
% 0.41/0.60  thf('123', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('124', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.41/0.60          != (k2_relat_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['122', '123'])).
% 0.41/0.60  thf('125', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['115', '124'])).
% 0.41/0.60  thf('126', plain,
% 0.41/0.60      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60           (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.41/0.60         | ~ (l1_struct_0 @ sk_B)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['106', '125'])).
% 0.41/0.60  thf('127', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('128', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('129', plain,
% 0.41/0.60      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.41/0.60  thf('130', plain,
% 0.41/0.60      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['105', '129'])).
% 0.41/0.60  thf('131', plain,
% 0.41/0.60      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.41/0.60         | ~ (v1_relat_1 @ sk_C)
% 0.41/0.60         | ~ (v1_funct_1 @ sk_C)
% 0.41/0.60         | ~ (v2_funct_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['94', '130'])).
% 0.41/0.60  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.60      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.60  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('134', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('135', plain,
% 0.41/0.60      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.41/0.60         <= (~
% 0.41/0.60             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60                = (k2_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.41/0.60  thf('136', plain,
% 0.41/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          = (k2_struct_0 @ sk_B)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['135'])).
% 0.41/0.60  thf('137', plain,
% 0.41/0.60      (~
% 0.41/0.60       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          = (k2_struct_0 @ sk_A))) | 
% 0.41/0.60       ~
% 0.41/0.60       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          = (k2_struct_0 @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['73'])).
% 0.41/0.60  thf('138', plain,
% 0.41/0.60      (~
% 0.41/0.60       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.60          = (k2_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['136', '137'])).
% 0.41/0.60  thf('139', plain,
% 0.41/0.60      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['93', '138'])).
% 0.41/0.60  thf('140', plain,
% 0.41/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['102'])).
% 0.41/0.60  thf('141', plain,
% 0.41/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.60         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.41/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.60  thf('142', plain,
% 0.41/0.60      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.60         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['140', '141'])).
% 0.41/0.60  thf('143', plain,
% 0.41/0.60      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['139', '142'])).
% 0.41/0.60  thf('144', plain,
% 0.41/0.60      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['71', '143'])).
% 0.41/0.60  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.60      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.60  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('148', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.41/0.60  thf('149', plain,
% 0.41/0.60      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.41/0.60        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['70', '148'])).
% 0.41/0.60  thf('150', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['149'])).
% 0.41/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.60  thf('151', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('152', plain, ($false),
% 0.41/0.60      inference('demod', [status(thm)], ['13', '150', '151'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
