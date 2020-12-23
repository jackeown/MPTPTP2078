%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K3mttx7dgH

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  290 (1942 expanded)
%              Number of leaves         :   39 ( 577 expanded)
%              Depth                    :   42
%              Number of atoms          : 2609 (41809 expanded)
%              Number of equality atoms :  113 (1213 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('17',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('33',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','36'])).

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
    inference(clc,[status(thm)],['31','41'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','52'])).

thf('54',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','41'])).

thf('56',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('62',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','68'])).

thf('70',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('72',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','69'])).

thf('73',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','69'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('75',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','70','71','72','73','74'])).

thf('76',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

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

thf('83',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('109',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','85','96','97','109'])).

thf('111',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['75','111'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('113',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

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

thf('115',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('119',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('126',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('127',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('130',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('135',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X22 ) @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('136',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('139',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('142',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('144',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('145',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('147',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('148',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('149',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('150',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('151',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('152',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['148','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('161',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('162',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('163',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('164',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','68'])).

thf('166',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('167',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('168',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('170',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != X16 )
      | ( v1_partfun1 @ X17 @ X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('171',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v4_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
      | ( v1_partfun1 @ X17 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['169','171'])).

thf('173',plain,(
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
    inference('sup-',[status(thm)],['168','172'])).

thf('174',plain,(
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
    inference('sup-',[status(thm)],['167','173'])).

thf('175',plain,(
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
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['166','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['165','177'])).

thf('179',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['164','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['163','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['162','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['161','198'])).

thf('200',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['199','200','201','202'])).

thf('204',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('205',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('207',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','68'])).

thf('208',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['160','208'])).

thf('210',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','68'])).

thf('211',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['209','210','211','212','213','214'])).

thf('216',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['159','215'])).

thf('217',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['132'])).

thf('218',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['147','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['146','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['145','228'])).

thf('230',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','133','142','229'])).

thf('231',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['113','231'])).

thf('233',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('234',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['232','233','234','235'])).

thf('237',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['112','236'])).

thf('238',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','237'])).

thf('239',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

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

thf('240',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_funct_2 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('241',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_funct_2 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['239','241'])).

thf('243',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('244',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('247',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    $false ),
    inference(demod,[status(thm)],['238','245','246','247','248'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K3mttx7dgH
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:57:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 221 iterations in 0.093s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.55  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.55  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(t65_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X6 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X6)
% 0.20/0.55          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.20/0.55          | ~ (v1_funct_1 @ X6)
% 0.20/0.55          | ~ (v1_relat_1 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.20/0.55  thf(d3_struct_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf(t64_tops_2, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_struct_0 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                 ( m1_subset_1 @
% 0.20/0.55                   C @ 
% 0.20/0.55                   ( k1_zfmisc_1 @
% 0.20/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55               ( ( ( ( k2_relset_1 @
% 0.20/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.20/0.55                     ( k2_struct_0 @ B ) ) & 
% 0.20/0.55                   ( v2_funct_1 @ C ) ) =>
% 0.20/0.55                 ( r2_funct_2 @
% 0.20/0.55                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.55                   ( k2_tops_2 @
% 0.20/0.55                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.55                     ( k2_tops_2 @
% 0.20/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.20/0.55                   C ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( l1_struct_0 @ A ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.55                    ( v1_funct_2 @
% 0.20/0.55                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                    ( m1_subset_1 @
% 0.20/0.55                      C @ 
% 0.20/0.55                      ( k1_zfmisc_1 @
% 0.20/0.55                        ( k2_zfmisc_1 @
% 0.20/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                  ( ( ( ( k2_relset_1 @
% 0.20/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.20/0.55                        ( k2_struct_0 @ B ) ) & 
% 0.20/0.55                      ( v2_funct_1 @ C ) ) =>
% 0.20/0.55                    ( r2_funct_2 @
% 0.20/0.55                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.55                      ( k2_tops_2 @
% 0.20/0.55                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.55                        ( k2_tops_2 @
% 0.20/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.20/0.55                      C ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.20/0.55          sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.20/0.55           sk_C)
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.20/0.55          sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.20/0.55           sk_C)
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.55  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.20/0.55          sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ 
% 0.20/0.55         (k1_zfmisc_1 @ 
% 0.20/0.55          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.20/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['14', '19'])).
% 0.20/0.55  thf(cc5_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.55       ( ![C:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.55             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.55          | (v1_partfun1 @ X13 @ X14)
% 0.20/0.55          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.20/0.55          | ~ (v1_funct_1 @ X13)
% 0.20/0.55          | (v1_xboole_0 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.20/0.55        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.20/0.55        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '23', '30'])).
% 0.20/0.55  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf(fc2_struct_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X26 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.20/0.55          | ~ (l1_struct_0 @ X26)
% 0.20/0.55          | (v2_struct_0 @ X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.20/0.55          | ~ (l1_struct_0 @ X0)
% 0.20/0.55          | (v2_struct_0 @ X0)
% 0.20/0.55          | ~ (l1_struct_0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X0)
% 0.20/0.55          | ~ (l1_struct_0 @ X0)
% 0.20/0.55          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.55        | (v2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['32', '36'])).
% 0.20/0.55  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.55  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('41', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('42', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['31', '41'])).
% 0.20/0.55  thf(d4_partfun1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.55       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (v1_partfun1 @ X17 @ X16)
% 0.20/0.55          | ((k1_relat_1 @ X17) = (X16))
% 0.20/0.55          | ~ (v4_relat_1 @ X17 @ X16)
% 0.20/0.55          | ~ (v1_relat_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc2_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.55          | (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ 
% 0.20/0.55           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v1_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf(fc6_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.55  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc2_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((v4_relat_1 @ X7 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.55  thf('52', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.55  thf('53', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['44', '49', '52'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('55', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['31', '41'])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup+', [status(thm)], ['54', '55'])).
% 0.20/0.55  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('58', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (v1_partfun1 @ X17 @ X16)
% 0.20/0.55          | ((k1_relat_1 @ X17) = (X16))
% 0.20/0.55          | ~ (v4_relat_1 @ X17 @ X16)
% 0.20/0.55          | ~ (v1_relat_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.20/0.55        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.55  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ 
% 0.20/0.55         (k1_zfmisc_1 @ 
% 0.20/0.55          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.55  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((v4_relat_1 @ X7 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.55  thf('68', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.55  thf('69', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '61', '68'])).
% 0.20/0.55  thf('70', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['53', '69'])).
% 0.20/0.55  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('72', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['53', '69'])).
% 0.20/0.55  thf('73', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['53', '69'])).
% 0.20/0.55  thf('74', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.20/0.55          sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '70', '71', '72', '73', '74'])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ 
% 0.20/0.55         (k1_zfmisc_1 @ 
% 0.20/0.55          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['76', '77'])).
% 0.20/0.55  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.55  thf('81', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.55  thf(d4_tops_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.20/0.55         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.55         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.20/0.55          | ~ (v2_funct_1 @ X29)
% 0.20/0.55          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.20/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.20/0.55          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.20/0.55          | ~ (v1_funct_1 @ X29))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.20/0.55        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55            = (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55            != (k2_relat_1 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.55  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup+', [status(thm)], ['87', '88'])).
% 0.20/0.55  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('91', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['86', '91'])).
% 0.20/0.55  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('94', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['92', '93'])).
% 0.20/0.55  thf('95', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('96', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.55  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('99', plain,
% 0.20/0.55      (![X25 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('100', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('101', plain,
% 0.20/0.55      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55          = (k2_struct_0 @ sk_B))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup+', [status(thm)], ['99', '100'])).
% 0.20/0.55  thf('102', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('103', plain,
% 0.20/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['101', '102'])).
% 0.20/0.55  thf('104', plain,
% 0.20/0.55      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55          = (k2_struct_0 @ sk_B))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['98', '103'])).
% 0.20/0.55  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('106', plain,
% 0.20/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['104', '105'])).
% 0.20/0.55  thf('107', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('108', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('109', plain,
% 0.20/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55         = (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.20/0.55  thf('110', plain,
% 0.20/0.55      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55          = (k2_funct_1 @ sk_C))
% 0.20/0.55        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['84', '85', '96', '97', '109'])).
% 0.20/0.55  thf('111', plain,
% 0.20/0.55      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55         = (k2_funct_1 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['110'])).
% 0.20/0.55  thf('112', plain,
% 0.20/0.55      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55           (k2_funct_1 @ sk_C)) @ 
% 0.20/0.55          sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['75', '111'])).
% 0.20/0.55  thf(fc6_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.20/0.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.55         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.55  thf('113', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.55  thf(t31_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.20/0.55         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.20/0.55           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.20/0.55           ( m1_subset_1 @
% 0.20/0.55             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('115', plain,
% 0.20/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X22)
% 0.20/0.55          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.20/0.55          | (m1_subset_1 @ (k2_funct_1 @ X22) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.20/0.55          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.20/0.55          | ~ (v1_funct_1 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.20/0.55  thf('116', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.20/0.55        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.55           (k1_zfmisc_1 @ 
% 0.20/0.55            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.20/0.55        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55            != (k2_relat_1 @ sk_C))
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.55  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('118', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.55  thf('119', plain,
% 0.20/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55         = (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.20/0.55  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('121', plain,
% 0.20/0.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.55         (k1_zfmisc_1 @ 
% 0.20/0.55          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.20/0.55        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 0.20/0.55  thf('122', plain,
% 0.20/0.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['121'])).
% 0.20/0.55  thf('123', plain,
% 0.20/0.55      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.55         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.20/0.55          | ~ (v2_funct_1 @ X29)
% 0.20/0.55          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.20/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.20/0.55          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.20/0.55          | ~ (v1_funct_1 @ X29))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.20/0.55  thf('124', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.55             (k2_struct_0 @ sk_A))
% 0.20/0.55        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.20/0.55        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['122', '123'])).
% 0.20/0.55  thf('125', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.55  thf('126', plain,
% 0.20/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X22)
% 0.20/0.55          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.20/0.55          | (v1_funct_1 @ (k2_funct_1 @ X22))
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.20/0.55          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.20/0.55          | ~ (v1_funct_1 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.20/0.55  thf('127', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.20/0.55        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55            != (k2_relat_1 @ sk_C))
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['125', '126'])).
% 0.20/0.55  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('129', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.55  thf('130', plain,
% 0.20/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55         = (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.20/0.55  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('132', plain,
% 0.20/0.55      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 0.20/0.55  thf('133', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['132'])).
% 0.20/0.55  thf('134', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.55  thf('135', plain,
% 0.20/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X22)
% 0.20/0.55          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.20/0.55          | (v1_funct_2 @ (k2_funct_1 @ X22) @ X23 @ X24)
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.20/0.55          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.20/0.55          | ~ (v1_funct_1 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.20/0.55  thf('136', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.20/0.55        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.55           (k2_struct_0 @ sk_A))
% 0.20/0.55        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55            != (k2_relat_1 @ sk_C))
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['134', '135'])).
% 0.20/0.55  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('138', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.55  thf('139', plain,
% 0.20/0.55      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.55         = (k2_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.20/0.55  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('141', plain,
% 0.20/0.55      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.55         (k2_struct_0 @ sk_A))
% 0.20/0.55        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 0.20/0.55  thf('142', plain,
% 0.20/0.55      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.55        (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['141'])).
% 0.20/0.55  thf('143', plain,
% 0.20/0.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['121'])).
% 0.20/0.55  thf('144', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.20/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.55  thf('145', plain,
% 0.20/0.55      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['143', '144'])).
% 0.20/0.55  thf('146', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('147', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('148', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('149', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('150', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('151', plain,
% 0.20/0.55      (![X6 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X6)
% 0.20/0.55          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.20/0.55          | ~ (v1_funct_1 @ X6)
% 0.20/0.55          | ~ (v1_relat_1 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.20/0.55  thf(t55_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.55       ( ( v2_funct_1 @ A ) =>
% 0.20/0.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.20/0.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('152', plain,
% 0.20/0.55      (![X5 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X5)
% 0.20/0.55          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.20/0.55          | ~ (v1_funct_1 @ X5)
% 0.20/0.55          | ~ (v1_relat_1 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.55  thf('153', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['151', '152'])).
% 0.20/0.55  thf('154', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['150', '153'])).
% 0.20/0.55  thf('155', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['154'])).
% 0.20/0.55  thf('156', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['149', '155'])).
% 0.20/0.55  thf('157', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['156'])).
% 0.20/0.55  thf('158', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['148', '157'])).
% 0.20/0.55  thf('159', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['158'])).
% 0.20/0.55  thf('160', plain,
% 0.20/0.55      (![X6 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X6)
% 0.20/0.55          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.20/0.55          | ~ (v1_funct_1 @ X6)
% 0.20/0.55          | ~ (v1_relat_1 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.20/0.55  thf('161', plain,
% 0.20/0.55      (![X6 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X6)
% 0.20/0.55          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.20/0.55          | ~ (v1_funct_1 @ X6)
% 0.20/0.55          | ~ (v1_relat_1 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.20/0.55  thf('162', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('163', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('164', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('165', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '61', '68'])).
% 0.20/0.55  thf('166', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.20/0.55          | ~ (v2_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_funct_1 @ X4)
% 0.20/0.55          | ~ (v1_relat_1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.20/0.55  thf('167', plain,
% 0.20/0.55      (![X5 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X5)
% 0.20/0.55          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.20/0.55          | ~ (v1_funct_1 @ X5)
% 0.20/0.55          | ~ (v1_relat_1 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.55  thf('168', plain,
% 0.20/0.55      (![X6 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X6)
% 0.20/0.55          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.20/0.55          | ~ (v1_funct_1 @ X6)
% 0.20/0.55          | ~ (v1_relat_1 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.20/0.55  thf('169', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['158'])).
% 0.20/0.55  thf('170', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (((k1_relat_1 @ X17) != (X16))
% 0.20/0.55          | (v1_partfun1 @ X17 @ X16)
% 0.20/0.55          | ~ (v4_relat_1 @ X17 @ X16)
% 0.20/0.55          | ~ (v1_relat_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.55  thf('171', plain,
% 0.20/0.55      (![X17 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X17)
% 0.20/0.55          | ~ (v4_relat_1 @ X17 @ (k1_relat_1 @ X17))
% 0.20/0.55          | (v1_partfun1 @ X17 @ (k1_relat_1 @ X17)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['170'])).
% 0.20/0.55  thf('172', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['169', '171'])).
% 0.20/0.55  thf('173', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.20/0.55          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.20/0.55             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['168', '172'])).
% 0.20/0.55  thf('174', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.20/0.55             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['167', '173'])).
% 0.20/0.55  thf('175', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.20/0.55          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.20/0.55             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['174'])).
% 0.20/0.55  thf('176', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.20/0.55             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['166', '175'])).
% 0.20/0.55  thf('177', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.20/0.55           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['176'])).
% 0.20/0.55  thf('178', plain,
% 0.20/0.55      ((~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.20/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.20/0.55           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['165', '177'])).
% 0.20/0.55  thf('179', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.55  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('183', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.20/0.55           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.20/0.55      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 0.20/0.55  thf('184', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.20/0.55           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.20/0.55        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['164', '183'])).
% 0.20/0.55  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('187', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('188', plain,
% 0.20/0.55      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.20/0.55         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.20/0.55        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['184', '185', '186', '187'])).
% 0.20/0.55  thf('189', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.20/0.55           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['163', '188'])).
% 0.20/0.55  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('193', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.20/0.55           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.20/0.55      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 0.20/0.55  thf('194', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.20/0.55           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['162', '193'])).
% 0.20/0.55  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('198', plain,
% 0.20/0.55      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.20/0.55        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 0.20/0.55  thf('199', plain,
% 0.20/0.55      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup+', [status(thm)], ['161', '198'])).
% 0.20/0.55  thf('200', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('202', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('203', plain,
% 0.20/0.55      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['199', '200', '201', '202'])).
% 0.20/0.55  thf('204', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (v1_partfun1 @ X17 @ X16)
% 0.20/0.55          | ((k1_relat_1 @ X17) = (X16))
% 0.20/0.55          | ~ (v4_relat_1 @ X17 @ X16)
% 0.20/0.55          | ~ (v1_relat_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.55  thf('205', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v4_relat_1 @ sk_C @ 
% 0.20/0.55             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.20/0.55        | ((k1_relat_1 @ sk_C)
% 0.20/0.55            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['203', '204'])).
% 0.20/0.55  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('207', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '61', '68'])).
% 0.20/0.55  thf('208', plain,
% 0.20/0.55      ((~ (v4_relat_1 @ sk_C @ 
% 0.20/0.55           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.20/0.55        | ((k2_struct_0 @ sk_A)
% 0.20/0.55            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.20/0.55      inference('demod', [status(thm)], ['205', '206', '207'])).
% 0.20/0.55  thf('209', plain,
% 0.20/0.55      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | ((k2_struct_0 @ sk_A)
% 0.20/0.55            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['160', '208'])).
% 0.20/0.55  thf('210', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '61', '68'])).
% 0.20/0.55  thf('211', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.55  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('215', plain,
% 0.20/0.55      (((k2_struct_0 @ sk_A)
% 0.20/0.55         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)],
% 0.20/0.55                ['209', '210', '211', '212', '213', '214'])).
% 0.20/0.55  thf('216', plain,
% 0.20/0.55      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.20/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['159', '215'])).
% 0.20/0.55  thf('217', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['132'])).
% 0.20/0.55  thf('218', plain,
% 0.20/0.55      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.20/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['216', '217'])).
% 0.20/0.55  thf('219', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['147', '218'])).
% 0.20/0.55  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('222', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('223', plain,
% 0.20/0.55      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 0.20/0.55  thf('224', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['146', '223'])).
% 0.20/0.55  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('228', plain,
% 0.20/0.55      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 0.20/0.55  thf('229', plain,
% 0.20/0.55      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['145', '228'])).
% 0.20/0.55  thf('230', plain,
% 0.20/0.55      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.20/0.55        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['124', '133', '142', '229'])).
% 0.20/0.55  thf('231', plain,
% 0.20/0.55      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.55        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['230'])).
% 0.20/0.55  thf('232', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['113', '231'])).
% 0.20/0.55  thf('233', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('234', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('235', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('236', plain,
% 0.20/0.55      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.20/0.55         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['232', '233', '234', '235'])).
% 0.20/0.55  thf('237', plain,
% 0.20/0.55      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['112', '236'])).
% 0.20/0.55  thf('238', plain,
% 0.20/0.55      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.55           sk_C)
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '237'])).
% 0.20/0.55  thf('239', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.55  thf(redefinition_r2_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.55         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.55  thf('240', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.55          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.20/0.55          | ~ (v1_funct_1 @ X18)
% 0.20/0.55          | ~ (v1_funct_1 @ X21)
% 0.20/0.55          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.20/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.55          | (r2_funct_2 @ X19 @ X20 @ X18 @ X21)
% 0.20/0.55          | ((X18) != (X21)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.20/0.55  thf('241', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.55         ((r2_funct_2 @ X19 @ X20 @ X21 @ X21)
% 0.20/0.55          | ~ (v1_funct_1 @ X21)
% 0.20/0.55          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.20/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['240'])).
% 0.20/0.55  thf('242', plain,
% 0.20/0.55      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.55           sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['239', '241'])).
% 0.20/0.55  thf('243', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.55  thf('244', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('245', plain,
% 0.20/0.55      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['242', '243', '244'])).
% 0.20/0.55  thf('246', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('247', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('248', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('249', plain, ($false),
% 0.20/0.55      inference('demod', [status(thm)], ['238', '245', '246', '247', '248'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
