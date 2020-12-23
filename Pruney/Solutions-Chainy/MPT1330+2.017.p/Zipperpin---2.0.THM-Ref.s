%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qn6pVPztF2

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:44 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 311 expanded)
%              Number of leaves         :   42 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          : 1060 (4372 expanded)
%              Number of equality atoms :   99 ( 338 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
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

thf('1',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k8_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k10_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v5_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ X19 @ ( k6_relat_1 @ X20 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( u1_struct_0 @ sk_B ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( u1_struct_0 @ sk_B ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('28',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('42',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ( v1_partfun1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('43',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X34 @ X32 )
      | ( v1_partfun1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('49',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','53'])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('66',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('67',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('69',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k8_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k10_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('77',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('79',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('80',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('82',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('83',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('86',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74','75','92'])).

thf('94',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('96',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['64','96'])).

thf('98',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','97'])).

thf('99',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','11','98'])).

thf('100',plain,(
    $false ),
    inference(simplify,[status(thm)],['99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qn6pVPztF2
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 21:08:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.84/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.05  % Solved by: fo/fo7.sh
% 0.84/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.05  % done 1073 iterations in 0.591s
% 0.84/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.05  % SZS output start Refutation
% 0.84/1.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.84/1.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.84/1.05  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.84/1.05  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.84/1.05  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.84/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.05  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.05  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.84/1.05  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.84/1.05  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.84/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.05  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.84/1.05  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.84/1.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.05  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.84/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.84/1.05  thf(d3_struct_0, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.84/1.05  thf('0', plain,
% 0.84/1.05      (![X35 : $i]:
% 0.84/1.05         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.84/1.05  thf(t52_tops_2, conjecture,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( l1_struct_0 @ A ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( l1_struct_0 @ B ) =>
% 0.84/1.05           ( ![C:$i]:
% 0.84/1.05             ( ( ( v1_funct_1 @ C ) & 
% 0.84/1.05                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.84/1.05                 ( m1_subset_1 @
% 0.84/1.05                   C @ 
% 0.84/1.05                   ( k1_zfmisc_1 @
% 0.84/1.05                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.84/1.05               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.84/1.05                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.84/1.05                 ( ( k8_relset_1 @
% 0.84/1.05                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.84/1.05                     ( k2_struct_0 @ B ) ) =
% 0.84/1.05                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.84/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.05    (~( ![A:$i]:
% 0.84/1.05        ( ( l1_struct_0 @ A ) =>
% 0.84/1.05          ( ![B:$i]:
% 0.84/1.05            ( ( l1_struct_0 @ B ) =>
% 0.84/1.05              ( ![C:$i]:
% 0.84/1.05                ( ( ( v1_funct_1 @ C ) & 
% 0.84/1.05                    ( v1_funct_2 @
% 0.84/1.05                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.84/1.05                    ( m1_subset_1 @
% 0.84/1.05                      C @ 
% 0.84/1.05                      ( k1_zfmisc_1 @
% 0.84/1.05                        ( k2_zfmisc_1 @
% 0.84/1.05                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.84/1.05                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.84/1.05                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.84/1.05                    ( ( k8_relset_1 @
% 0.84/1.05                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.84/1.05                        ( k2_struct_0 @ B ) ) =
% 0.84/1.05                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.84/1.05    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.84/1.05  thf('1', plain,
% 0.84/1.05      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.84/1.05         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('2', plain,
% 0.84/1.05      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.84/1.05          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.84/1.05        | ~ (l1_struct_0 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['0', '1'])).
% 0.84/1.05  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('4', plain,
% 0.84/1.05      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.84/1.05         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.84/1.05  thf('5', plain,
% 0.84/1.05      (![X35 : $i]:
% 0.84/1.05         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.84/1.05  thf('6', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ 
% 0.84/1.05        (k1_zfmisc_1 @ 
% 0.84/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('7', plain,
% 0.84/1.05      (((m1_subset_1 @ sk_C @ 
% 0.84/1.05         (k1_zfmisc_1 @ 
% 0.84/1.05          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.84/1.05        | ~ (l1_struct_0 @ sk_A))),
% 0.84/1.05      inference('sup+', [status(thm)], ['5', '6'])).
% 0.84/1.05  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('9', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ 
% 0.84/1.05        (k1_zfmisc_1 @ 
% 0.84/1.05         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.84/1.05      inference('demod', [status(thm)], ['7', '8'])).
% 0.84/1.05  thf(redefinition_k8_relset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.05       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.84/1.05  thf('10', plain,
% 0.84/1.05      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.84/1.05          | ((k8_relset_1 @ X27 @ X28 @ X26 @ X29) = (k10_relat_1 @ X26 @ X29)))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.84/1.05  thf('11', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.84/1.05           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['9', '10'])).
% 0.84/1.05  thf('12', plain,
% 0.84/1.05      (![X35 : $i]:
% 0.84/1.05         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.84/1.05  thf('13', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ 
% 0.84/1.05        (k1_zfmisc_1 @ 
% 0.84/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(cc2_relset_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.05       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.84/1.05  thf('14', plain,
% 0.84/1.05      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.05         ((v5_relat_1 @ X23 @ X25)
% 0.84/1.05          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.84/1.05  thf('15', plain, ((v5_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.84/1.05      inference('sup-', [status(thm)], ['13', '14'])).
% 0.84/1.05  thf(d19_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ B ) =>
% 0.84/1.05       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.84/1.05  thf('16', plain,
% 0.84/1.05      (![X11 : $i, X12 : $i]:
% 0.84/1.05         (~ (v5_relat_1 @ X11 @ X12)
% 0.84/1.05          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.84/1.05          | ~ (v1_relat_1 @ X11))),
% 0.84/1.05      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.84/1.05  thf('17', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ sk_C)
% 0.84/1.05        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.05  thf('18', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ 
% 0.84/1.05        (k1_zfmisc_1 @ 
% 0.84/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(cc2_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.84/1.05  thf('19', plain,
% 0.84/1.05      (![X7 : $i, X8 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.84/1.05          | (v1_relat_1 @ X7)
% 0.84/1.05          | ~ (v1_relat_1 @ X8))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.84/1.05  thf('20', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ 
% 0.84/1.05           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.84/1.05        | (v1_relat_1 @ sk_C))),
% 0.84/1.05      inference('sup-', [status(thm)], ['18', '19'])).
% 0.84/1.05  thf(fc6_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.84/1.05  thf('21', plain,
% 0.84/1.05      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.84/1.05  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.05      inference('demod', [status(thm)], ['20', '21'])).
% 0.84/1.05  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.84/1.05      inference('demod', [status(thm)], ['17', '22'])).
% 0.84/1.05  thf(t79_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ B ) =>
% 0.84/1.05       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.84/1.05         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.84/1.05  thf('24', plain,
% 0.84/1.05      (![X19 : $i, X20 : $i]:
% 0.84/1.05         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.84/1.05          | ((k5_relat_1 @ X19 @ (k6_relat_1 @ X20)) = (X19))
% 0.84/1.05          | ~ (v1_relat_1 @ X19))),
% 0.84/1.05      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.84/1.05  thf('25', plain,
% 0.84/1.05      ((~ (v1_relat_1 @ sk_C)
% 0.84/1.05        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ (u1_struct_0 @ sk_B))) = (sk_C)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['23', '24'])).
% 0.84/1.05  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.05      inference('demod', [status(thm)], ['20', '21'])).
% 0.84/1.05  thf('27', plain,
% 0.84/1.05      (((k5_relat_1 @ sk_C @ (k6_relat_1 @ (u1_struct_0 @ sk_B))) = (sk_C))),
% 0.84/1.05      inference('demod', [status(thm)], ['25', '26'])).
% 0.84/1.05  thf(t71_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.84/1.05       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.84/1.05  thf('28', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.84/1.05      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.84/1.05  thf(t182_relat_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ A ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( v1_relat_1 @ B ) =>
% 0.84/1.05           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.84/1.05             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.84/1.05  thf('29', plain,
% 0.84/1.05      (![X15 : $i, X16 : $i]:
% 0.84/1.05         (~ (v1_relat_1 @ X15)
% 0.84/1.05          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 0.84/1.05              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 0.84/1.05          | ~ (v1_relat_1 @ X16))),
% 0.84/1.05      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.84/1.05  thf('30', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.84/1.05            = (k10_relat_1 @ X1 @ X0))
% 0.84/1.05          | ~ (v1_relat_1 @ X1)
% 0.84/1.05          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['28', '29'])).
% 0.84/1.05  thf(fc3_funct_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.84/1.05       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.84/1.05  thf('31', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.84/1.05  thf('32', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.84/1.05            = (k10_relat_1 @ X1 @ X0))
% 0.84/1.05          | ~ (v1_relat_1 @ X1))),
% 0.84/1.05      inference('demod', [status(thm)], ['30', '31'])).
% 0.84/1.05  thf('33', plain,
% 0.84/1.05      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_C))),
% 0.84/1.05      inference('sup+', [status(thm)], ['27', '32'])).
% 0.84/1.05  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.05      inference('demod', [status(thm)], ['20', '21'])).
% 0.84/1.05  thf('35', plain,
% 0.84/1.05      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (u1_struct_0 @ sk_B)))),
% 0.84/1.05      inference('demod', [status(thm)], ['33', '34'])).
% 0.84/1.05  thf('36', plain,
% 0.84/1.05      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))
% 0.84/1.05        | ~ (l1_struct_0 @ sk_B))),
% 0.84/1.05      inference('sup+', [status(thm)], ['12', '35'])).
% 0.84/1.05  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('38', plain,
% 0.84/1.05      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 0.84/1.05      inference('demod', [status(thm)], ['36', '37'])).
% 0.84/1.05  thf('39', plain,
% 0.84/1.05      (![X35 : $i]:
% 0.84/1.05         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.84/1.05  thf('40', plain,
% 0.84/1.05      (![X35 : $i]:
% 0.84/1.05         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.84/1.05      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.84/1.05  thf('41', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ 
% 0.84/1.05        (k1_zfmisc_1 @ 
% 0.84/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(t132_funct_2, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( ( v1_funct_1 @ C ) & 
% 0.84/1.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.05       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.05           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.05         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.84/1.05           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.84/1.05  thf('42', plain,
% 0.84/1.05      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.84/1.05         (((X32) = (k1_xboole_0))
% 0.84/1.05          | ~ (v1_funct_1 @ X33)
% 0.84/1.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.84/1.05          | (v1_partfun1 @ X33 @ X34)
% 0.84/1.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.84/1.05          | ~ (v1_funct_2 @ X33 @ X34 @ X32)
% 0.84/1.05          | ~ (v1_funct_1 @ X33))),
% 0.84/1.05      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.84/1.05  thf('43', plain,
% 0.84/1.05      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.84/1.05         (~ (v1_funct_2 @ X33 @ X34 @ X32)
% 0.84/1.05          | (v1_partfun1 @ X33 @ X34)
% 0.84/1.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.84/1.05          | ~ (v1_funct_1 @ X33)
% 0.84/1.05          | ((X32) = (k1_xboole_0)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['42'])).
% 0.84/1.05  thf('44', plain,
% 0.84/1.05      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.84/1.05        | ~ (v1_funct_1 @ sk_C)
% 0.84/1.05        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['41', '43'])).
% 0.84/1.05  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('46', plain,
% 0.84/1.05      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('47', plain,
% 0.84/1.05      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.84/1.05        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.84/1.05  thf(d4_partfun1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.84/1.05       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.84/1.05  thf('48', plain,
% 0.84/1.05      (![X30 : $i, X31 : $i]:
% 0.84/1.05         (~ (v1_partfun1 @ X31 @ X30)
% 0.84/1.05          | ((k1_relat_1 @ X31) = (X30))
% 0.84/1.05          | ~ (v4_relat_1 @ X31 @ X30)
% 0.84/1.05          | ~ (v1_relat_1 @ X31))),
% 0.84/1.05      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.84/1.05  thf('49', plain,
% 0.84/1.05      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.84/1.05        | ~ (v1_relat_1 @ sk_C)
% 0.84/1.05        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['47', '48'])).
% 0.84/1.05  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.05      inference('demod', [status(thm)], ['20', '21'])).
% 0.84/1.05  thf('51', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ 
% 0.84/1.05        (k1_zfmisc_1 @ 
% 0.84/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('52', plain,
% 0.84/1.05      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.05         ((v4_relat_1 @ X23 @ X24)
% 0.84/1.05          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.84/1.05  thf('53', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['51', '52'])).
% 0.84/1.05  thf('54', plain,
% 0.84/1.05      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.84/1.05        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['49', '50', '53'])).
% 0.84/1.05  thf('55', plain,
% 0.84/1.05      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.84/1.05        | ~ (l1_struct_0 @ sk_B)
% 0.84/1.05        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['40', '54'])).
% 0.84/1.05  thf('56', plain, ((l1_struct_0 @ sk_B)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('57', plain,
% 0.84/1.05      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.84/1.05        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['55', '56'])).
% 0.84/1.05  thf('58', plain,
% 0.84/1.05      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.84/1.05        | ~ (l1_struct_0 @ sk_A)
% 0.84/1.05        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['39', '57'])).
% 0.84/1.05  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('60', plain,
% 0.84/1.05      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.84/1.05        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.84/1.05      inference('demod', [status(thm)], ['58', '59'])).
% 0.84/1.05  thf('61', plain,
% 0.84/1.05      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.84/1.05        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('62', plain,
% 0.84/1.05      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.84/1.05         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.84/1.05      inference('split', [status(esa)], ['61'])).
% 0.84/1.05  thf('63', plain,
% 0.84/1.05      (((((k1_xboole_0) != (k1_xboole_0))
% 0.84/1.05         | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))))
% 0.84/1.05         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['60', '62'])).
% 0.84/1.05  thf('64', plain,
% 0.84/1.05      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))
% 0.84/1.05         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['63'])).
% 0.84/1.05  thf('65', plain,
% 0.84/1.05      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.05      inference('split', [status(esa)], ['61'])).
% 0.84/1.05  thf('66', plain,
% 0.84/1.05      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.84/1.05         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.84/1.05  thf('67', plain,
% 0.84/1.05      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.84/1.05          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['65', '66'])).
% 0.84/1.05  thf('68', plain,
% 0.84/1.05      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.05      inference('split', [status(esa)], ['61'])).
% 0.84/1.05  thf('69', plain,
% 0.84/1.05      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.84/1.05          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.05      inference('demod', [status(thm)], ['67', '68'])).
% 0.84/1.05  thf('70', plain,
% 0.84/1.05      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.05      inference('split', [status(esa)], ['61'])).
% 0.84/1.05  thf('71', plain,
% 0.84/1.05      ((m1_subset_1 @ sk_C @ 
% 0.84/1.05        (k1_zfmisc_1 @ 
% 0.84/1.05         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.84/1.05      inference('demod', [status(thm)], ['7', '8'])).
% 0.84/1.05  thf('72', plain,
% 0.84/1.05      (((m1_subset_1 @ sk_C @ 
% 0.84/1.05         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['70', '71'])).
% 0.84/1.05  thf('73', plain,
% 0.84/1.05      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.84/1.05          | ((k8_relset_1 @ X27 @ X28 @ X26 @ X29) = (k10_relat_1 @ X26 @ X29)))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.84/1.05  thf('74', plain,
% 0.84/1.05      ((![X0 : $i]:
% 0.84/1.05          ((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ X0)
% 0.84/1.05            = (k10_relat_1 @ sk_C @ X0)))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['72', '73'])).
% 0.84/1.05  thf('75', plain,
% 0.84/1.05      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 0.84/1.05      inference('demod', [status(thm)], ['36', '37'])).
% 0.84/1.05  thf('76', plain,
% 0.84/1.05      (((m1_subset_1 @ sk_C @ 
% 0.84/1.05         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.05      inference('sup+', [status(thm)], ['70', '71'])).
% 0.84/1.05  thf('77', plain,
% 0.84/1.05      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.05         ((v4_relat_1 @ X23 @ X24)
% 0.84/1.05          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.84/1.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.84/1.05  thf('78', plain,
% 0.84/1.05      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['76', '77'])).
% 0.84/1.05  thf(d18_relat_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( v1_relat_1 @ B ) =>
% 0.84/1.05       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.84/1.05  thf('79', plain,
% 0.84/1.05      (![X9 : $i, X10 : $i]:
% 0.84/1.05         (~ (v4_relat_1 @ X9 @ X10)
% 0.84/1.05          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.84/1.05          | ~ (v1_relat_1 @ X9))),
% 0.84/1.05      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.84/1.05  thf('80', plain,
% 0.84/1.05      (((~ (v1_relat_1 @ sk_C)
% 0.84/1.05         | (r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))
% 0.84/1.05         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['78', '79'])).
% 0.84/1.06  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.06      inference('demod', [status(thm)], ['20', '21'])).
% 0.84/1.06  thf('82', plain,
% 0.84/1.06      (((r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 0.84/1.06         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.06      inference('demod', [status(thm)], ['80', '81'])).
% 0.84/1.06  thf(t3_subset, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.84/1.06  thf('83', plain,
% 0.84/1.06      (![X4 : $i, X6 : $i]:
% 0.84/1.06         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.06  thf('84', plain,
% 0.84/1.06      (((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.84/1.06         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['82', '83'])).
% 0.84/1.06  thf(cc1_subset_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( v1_xboole_0 @ A ) =>
% 0.84/1.06       ( ![B:$i]:
% 0.84/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.84/1.06  thf('85', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]:
% 0.84/1.06         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.84/1.06          | (v1_xboole_0 @ X2)
% 0.84/1.06          | ~ (v1_xboole_0 @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.84/1.06  thf('86', plain,
% 0.84/1.06      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (k1_relat_1 @ sk_C))))
% 0.84/1.06         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['84', '85'])).
% 0.84/1.06  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.84/1.06  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.84/1.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.84/1.06  thf('88', plain,
% 0.84/1.06      (((v1_xboole_0 @ (k1_relat_1 @ sk_C)))
% 0.84/1.06         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.06      inference('demod', [status(thm)], ['86', '87'])).
% 0.84/1.06  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.84/1.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.84/1.06  thf(t8_boole, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.84/1.06  thf('90', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t8_boole])).
% 0.84/1.06  thf('91', plain,
% 0.84/1.06      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['89', '90'])).
% 0.84/1.06  thf('92', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k1_relat_1 @ sk_C)))
% 0.84/1.06         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['88', '91'])).
% 0.84/1.06  thf('93', plain,
% 0.84/1.06      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.84/1.06         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.84/1.06      inference('demod', [status(thm)], ['69', '74', '75', '92'])).
% 0.84/1.06  thf('94', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['93'])).
% 0.84/1.06  thf('95', plain,
% 0.84/1.06      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.84/1.06       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.84/1.06      inference('split', [status(esa)], ['61'])).
% 0.84/1.06  thf('96', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 0.84/1.06  thf('97', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.84/1.06      inference('simpl_trail', [status(thm)], ['64', '96'])).
% 0.84/1.06  thf('98', plain,
% 0.84/1.06      (((k2_struct_0 @ sk_A) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B)))),
% 0.84/1.06      inference('demod', [status(thm)], ['38', '97'])).
% 0.84/1.06  thf('99', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['4', '11', '98'])).
% 0.84/1.06  thf('100', plain, ($false), inference('simplify', [status(thm)], ['99'])).
% 0.84/1.06  
% 0.84/1.06  % SZS output end Refutation
% 0.84/1.06  
% 0.84/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
