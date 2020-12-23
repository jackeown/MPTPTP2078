%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HHmZrXWqnz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:13 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  310 (6389 expanded)
%              Number of leaves         :   44 (1886 expanded)
%              Depth                    :   35
%              Number of atoms          : 2930 (133420 expanded)
%              Number of equality atoms :  122 (3824 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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

thf('2',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('12',plain,(
    v5_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('34',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','30','32','33'])).

thf('35',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','47'])).

thf('49',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','30','32','33'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('50',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','55'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('64',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','55'])).

thf('66',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('72',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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

thf('77',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','78'])).

thf('80',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('81',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','30','32','33'])).

thf('83',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','34','80','81','82'])).

thf('84',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['102','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91','100','101','110'])).

thf('112',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['83','112'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('114',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

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

thf('116',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('120',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('127',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('131',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('136',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X29 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('137',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('140',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('141',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','134','143'])).

thf('145',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('146',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('147',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('148',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('150',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['142'])).

thf('151',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('153',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('154',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','78'])).

thf('156',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('157',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('158',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf(t51_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) )
              & ( v2_funct_1 @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('159',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) )
       != ( k2_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['157','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['156','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['155','167'])).

thf('169',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','78'])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('173',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169','170','171','172'])).

thf('174',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('175',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('176',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('178',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('180',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('183',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['178','183'])).

thf('185',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['173','184'])).

thf('186',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['154','185'])).

thf('187',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','186'])).

thf('188',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['145','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

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

thf('195',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_funct_2 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('201',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('202',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['199','200','201','202'])).

thf('204',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['193','203'])).

thf('205',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('206',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('207',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('208',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('210',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['142'])).

thf('211',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['154','185'])).

thf('213',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['205','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216','217','218'])).

thf('220',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('221',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('222',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X29 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('223',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('225',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['142'])).

thf('226',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['154','185'])).

thf('228',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['220','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['230','231','232','233'])).

thf('235',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['204','219','234'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('236',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('237',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('238',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_funct_2 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('239',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['237','239'])).

thf('241',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['230','231','232','233'])).

thf('242',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216','217','218'])).

thf('243',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['236','243'])).

thf('245',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['244','245','246','247'])).

thf('249',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','248'])).

thf('250',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['154','185'])).

thf('251',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','249','250'])).

thf('252',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['114','252'])).

thf('254',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf('255',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['253','254','255','256'])).

thf('258',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('259',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('260',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,(
    $false ),
    inference(demod,[status(thm)],['113','257','263'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HHmZrXWqnz
% 0.10/0.30  % Computer   : n007.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 15:20:36 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running portfolio for 600 s
% 0.10/0.30  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.10/0.30  % Number of cores: 8
% 0.10/0.30  % Python version: Python 3.6.8
% 0.10/0.30  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 427 iterations in 0.254s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.67  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.47/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.67  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.47/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.67  thf(d3_struct_0, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf(t64_tops_2, conjecture,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( l1_struct_0 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.47/0.67           ( ![C:$i]:
% 0.47/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.67                 ( m1_subset_1 @
% 0.47/0.67                   C @ 
% 0.47/0.67                   ( k1_zfmisc_1 @
% 0.47/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.67               ( ( ( ( k2_relset_1 @
% 0.47/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.47/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.47/0.67                   ( v2_funct_1 @ C ) ) =>
% 0.47/0.67                 ( r2_funct_2 @
% 0.47/0.67                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.47/0.67                   ( k2_tops_2 @
% 0.47/0.67                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.67                     ( k2_tops_2 @
% 0.47/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.47/0.67                   C ) ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i]:
% 0.47/0.67        ( ( l1_struct_0 @ A ) =>
% 0.47/0.67          ( ![B:$i]:
% 0.47/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.47/0.67              ( ![C:$i]:
% 0.47/0.67                ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.67                    ( v1_funct_2 @
% 0.47/0.67                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.67                    ( m1_subset_1 @
% 0.47/0.67                      C @ 
% 0.47/0.67                      ( k1_zfmisc_1 @
% 0.47/0.67                        ( k2_zfmisc_1 @
% 0.47/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.67                  ( ( ( ( k2_relset_1 @
% 0.47/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.47/0.67                        ( k2_struct_0 @ B ) ) & 
% 0.47/0.67                      ( v2_funct_1 @ C ) ) =>
% 0.47/0.67                    ( r2_funct_2 @
% 0.47/0.67                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.47/0.67                      ( k2_tops_2 @
% 0.47/0.67                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.67                        ( k2_tops_2 @
% 0.47/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.47/0.67                      C ) ) ) ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.67          sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.67           sk_C)
% 0.47/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.67  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.67          sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.67           sk_C)
% 0.47/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.67  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.67          sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['6', '7'])).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.67         ((v5_relat_1 @ X14 @ X16)
% 0.47/0.67          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.67  thf('12', plain, ((v5_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.67  thf(d19_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ B ) =>
% 0.47/0.67       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      (![X5 : $i, X6 : $i]:
% 0.47/0.67         (~ (v5_relat_1 @ X5 @ X6)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.47/0.67          | ~ (v1_relat_1 @ X5))),
% 0.47/0.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.67        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc2_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (![X3 : $i, X4 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.47/0.67          | (v1_relat_1 @ X3)
% 0.47/0.67          | ~ (v1_relat_1 @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ 
% 0.47/0.67           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.47/0.67        | (v1_relat_1 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.67  thf(fc6_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.67  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['14', '19'])).
% 0.47/0.67  thf(d10_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      (![X0 : $i, X2 : $i]:
% 0.47/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_relat_1 @ sk_C))
% 0.47/0.67        | ((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_relat_1 @ sk_C))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_B)
% 0.47/0.67        | ((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['9', '22'])).
% 0.47/0.67  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_relat_1 @ sk_C))
% 0.47/0.67        | ((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.67         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.47/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k2_relat_1 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['28', '29'])).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.67      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.67  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['28', '29'])).
% 0.47/0.67  thf('34', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['25', '30', '32', '33'])).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ 
% 0.47/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.47/0.67  thf(cc5_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.67       ( ![C:$i]:
% 0.47/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.47/0.67             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.47/0.67          | (v1_partfun1 @ X20 @ X21)
% 0.47/0.67          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.47/0.67          | ~ (v1_funct_1 @ X20)
% 0.47/0.67          | (v1_xboole_0 @ X22))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.67  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['43', '44'])).
% 0.47/0.67  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('47', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.67  thf('48', plain,
% 0.47/0.67      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['41', '42', '47'])).
% 0.47/0.67  thf('49', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['25', '30', '32', '33'])).
% 0.47/0.67  thf(fc2_struct_0, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.67       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      (![X33 : $i]:
% 0.47/0.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 0.47/0.67          | ~ (l1_struct_0 @ X33)
% 0.47/0.67          | (v2_struct_0 @ X33))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.67  thf('51', plain,
% 0.47/0.67      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | (v2_struct_0 @ sk_B)
% 0.47/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['49', '50'])).
% 0.47/0.67  thf('52', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('53', plain,
% 0.47/0.67      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['51', '52'])).
% 0.47/0.67  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('55', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('clc', [status(thm)], ['53', '54'])).
% 0.47/0.67  thf('56', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('clc', [status(thm)], ['48', '55'])).
% 0.47/0.67  thf(d4_partfun1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.67       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      (![X23 : $i, X24 : $i]:
% 0.47/0.67         (~ (v1_partfun1 @ X24 @ X23)
% 0.47/0.67          | ((k1_relat_1 @ X24) = (X23))
% 0.47/0.67          | ~ (v4_relat_1 @ X24 @ X23)
% 0.47/0.67          | ~ (v1_relat_1 @ X24))),
% 0.47/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.67  thf('58', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.67        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.67        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.67  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('60', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('61', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.67         ((v4_relat_1 @ X14 @ X15)
% 0.47/0.67          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.67  thf('62', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['60', '61'])).
% 0.47/0.67  thf('63', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['58', '59', '62'])).
% 0.47/0.67  thf('64', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('65', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('clc', [status(thm)], ['48', '55'])).
% 0.47/0.67  thf('66', plain,
% 0.47/0.67      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['64', '65'])).
% 0.47/0.67  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('68', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['66', '67'])).
% 0.47/0.67  thf('69', plain,
% 0.47/0.67      (![X23 : $i, X24 : $i]:
% 0.47/0.67         (~ (v1_partfun1 @ X24 @ X23)
% 0.47/0.67          | ((k1_relat_1 @ X24) = (X23))
% 0.47/0.67          | ~ (v4_relat_1 @ X24 @ X23)
% 0.47/0.67          | ~ (v1_relat_1 @ X24))),
% 0.47/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.67  thf('70', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.67        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.47/0.67        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['68', '69'])).
% 0.47/0.67  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('72', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('73', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('74', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ 
% 0.47/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['72', '73'])).
% 0.47/0.67  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('76', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.67  thf('77', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.67         ((v4_relat_1 @ X14 @ X15)
% 0.47/0.67          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.67  thf('78', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.67  thf('79', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['70', '71', '78'])).
% 0.47/0.67  thf('80', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['63', '79'])).
% 0.47/0.67  thf('81', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['63', '79'])).
% 0.47/0.67  thf('82', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['25', '30', '32', '33'])).
% 0.47/0.67  thf('83', plain,
% 0.47/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.67          sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['8', '34', '80', '81', '82'])).
% 0.47/0.67  thf('84', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('85', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.67  thf('86', plain,
% 0.47/0.67      (((m1_subset_1 @ sk_C @ 
% 0.47/0.67         (k1_zfmisc_1 @ 
% 0.47/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['84', '85'])).
% 0.47/0.67  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('88', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['86', '87'])).
% 0.47/0.67  thf(d4_tops_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.67       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.47/0.67         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.47/0.67  thf('89', plain,
% 0.47/0.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.47/0.67         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.47/0.67          | ~ (v2_funct_1 @ X36)
% 0.47/0.67          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.47/0.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.47/0.67          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.47/0.67          | ~ (v1_funct_1 @ X36))),
% 0.47/0.67      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.47/0.67  thf('90', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67            = (k2_funct_1 @ sk_C))
% 0.47/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67            != (k2_struct_0 @ sk_B)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['88', '89'])).
% 0.47/0.67  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('92', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('93', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('94', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('95', plain,
% 0.47/0.67      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['93', '94'])).
% 0.47/0.67  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('97', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['95', '96'])).
% 0.47/0.67  thf('98', plain,
% 0.47/0.67      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['92', '97'])).
% 0.47/0.67  thf('99', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('100', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['98', '99'])).
% 0.47/0.67  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('102', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('103', plain,
% 0.47/0.67      (![X32 : $i]:
% 0.47/0.67         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.67  thf('104', plain,
% 0.47/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('105', plain,
% 0.47/0.67      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67          = (k2_struct_0 @ sk_B))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['103', '104'])).
% 0.47/0.67  thf('106', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('107', plain,
% 0.47/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['105', '106'])).
% 0.47/0.67  thf('108', plain,
% 0.47/0.67      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67          = (k2_struct_0 @ sk_B))
% 0.47/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['102', '107'])).
% 0.47/0.67  thf('109', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('110', plain,
% 0.47/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['108', '109'])).
% 0.47/0.67  thf('111', plain,
% 0.47/0.67      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67          = (k2_funct_1 @ sk_C))
% 0.47/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.47/0.67      inference('demod', [status(thm)], ['90', '91', '100', '101', '110'])).
% 0.47/0.67  thf('112', plain,
% 0.47/0.67      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k2_funct_1 @ sk_C))),
% 0.47/0.67      inference('simplify', [status(thm)], ['111'])).
% 0.47/0.67  thf('113', plain,
% 0.47/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67           (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67          sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['83', '112'])).
% 0.47/0.67  thf(fc6_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.47/0.67       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.67         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.67         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.47/0.67  thf('114', plain,
% 0.47/0.67      (![X9 : $i]:
% 0.47/0.67         ((v2_funct_1 @ (k2_funct_1 @ X9))
% 0.47/0.67          | ~ (v2_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_relat_1 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.47/0.67  thf('115', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['86', '87'])).
% 0.47/0.67  thf(t31_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.67       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.47/0.67         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.47/0.67           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.47/0.67           ( m1_subset_1 @
% 0.47/0.67             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.47/0.67  thf('116', plain,
% 0.47/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X29)
% 0.47/0.67          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.47/0.67          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 0.47/0.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.47/0.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.47/0.67          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.47/0.67          | ~ (v1_funct_1 @ X29))),
% 0.47/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.67  thf('117', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.67           (k1_zfmisc_1 @ 
% 0.47/0.67            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.47/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67            != (k2_struct_0 @ sk_B))
% 0.47/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['115', '116'])).
% 0.47/0.67  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('119', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['98', '99'])).
% 0.47/0.67  thf('120', plain,
% 0.47/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['108', '109'])).
% 0.47/0.67  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('122', plain,
% 0.47/0.67      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.67         (k1_zfmisc_1 @ 
% 0.47/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.47/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.47/0.67      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 0.47/0.67  thf('123', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.67  thf('124', plain,
% 0.47/0.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.47/0.67         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.47/0.67          | ~ (v2_funct_1 @ X36)
% 0.47/0.67          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.47/0.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.47/0.67          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.47/0.67          | ~ (v1_funct_1 @ X36))),
% 0.47/0.67      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.47/0.67  thf('125', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.67        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67             (k2_struct_0 @ sk_A))
% 0.47/0.67        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.67        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['123', '124'])).
% 0.47/0.67  thf('126', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['86', '87'])).
% 0.47/0.67  thf('127', plain,
% 0.47/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X29)
% 0.47/0.67          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.47/0.67          | (v1_funct_1 @ (k2_funct_1 @ X29))
% 0.47/0.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.47/0.67          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.47/0.67          | ~ (v1_funct_1 @ X29))),
% 0.47/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.67  thf('128', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67            != (k2_struct_0 @ sk_B))
% 0.47/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['126', '127'])).
% 0.47/0.67  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('130', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['98', '99'])).
% 0.47/0.67  thf('131', plain,
% 0.47/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['108', '109'])).
% 0.47/0.67  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('133', plain,
% 0.47/0.67      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.47/0.67      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 0.47/0.67  thf('134', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.67      inference('simplify', [status(thm)], ['133'])).
% 0.47/0.67  thf('135', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['86', '87'])).
% 0.47/0.67  thf('136', plain,
% 0.47/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X29)
% 0.47/0.67          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.47/0.67          | (v1_funct_2 @ (k2_funct_1 @ X29) @ X30 @ X31)
% 0.47/0.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.47/0.67          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.47/0.67          | ~ (v1_funct_1 @ X29))),
% 0.47/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.67  thf('137', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67           (k2_struct_0 @ sk_A))
% 0.47/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67            != (k2_struct_0 @ sk_B))
% 0.47/0.67        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['135', '136'])).
% 0.47/0.67  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('139', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['98', '99'])).
% 0.47/0.67  thf('140', plain,
% 0.47/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.67         = (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['108', '109'])).
% 0.47/0.67  thf('141', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('142', plain,
% 0.47/0.67      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67         (k2_struct_0 @ sk_A))
% 0.47/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.47/0.67      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 0.47/0.67  thf('143', plain,
% 0.47/0.67      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67        (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('simplify', [status(thm)], ['142'])).
% 0.47/0.67  thf('144', plain,
% 0.47/0.67      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.67        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['125', '134', '143'])).
% 0.47/0.67  thf('145', plain,
% 0.47/0.67      (![X9 : $i]:
% 0.47/0.67         ((v2_funct_1 @ (k2_funct_1 @ X9))
% 0.47/0.67          | ~ (v2_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_relat_1 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.47/0.67  thf('146', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.67  thf('147', plain,
% 0.47/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X29)
% 0.47/0.67          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.47/0.67          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 0.47/0.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.47/0.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.47/0.67          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.47/0.67          | ~ (v1_funct_1 @ X29))),
% 0.47/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.67  thf('148', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.67        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67             (k2_struct_0 @ sk_A))
% 0.47/0.67        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67           (k1_zfmisc_1 @ 
% 0.47/0.67            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.47/0.67        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['146', '147'])).
% 0.47/0.67  thf('149', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.67      inference('simplify', [status(thm)], ['133'])).
% 0.47/0.67  thf('150', plain,
% 0.47/0.67      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67        (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('simplify', [status(thm)], ['142'])).
% 0.47/0.67  thf('151', plain,
% 0.47/0.67      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67         (k1_zfmisc_1 @ 
% 0.47/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.67        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.47/0.67        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.47/0.67  thf('152', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.67  thf('153', plain,
% 0.47/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.67         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.47/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.67  thf('154', plain,
% 0.47/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['152', '153'])).
% 0.47/0.67  thf('155', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['70', '71', '78'])).
% 0.47/0.67  thf('156', plain,
% 0.47/0.67      (![X9 : $i]:
% 0.47/0.67         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.47/0.67          | ~ (v2_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_relat_1 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.47/0.67  thf('157', plain,
% 0.47/0.67      (![X9 : $i]:
% 0.47/0.67         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.47/0.67          | ~ (v2_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_relat_1 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.47/0.67  thf(t59_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ( v2_funct_1 @ A ) =>
% 0.47/0.67         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.47/0.67             ( k2_relat_1 @ A ) ) & 
% 0.47/0.67           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.47/0.67             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.47/0.67  thf('158', plain,
% 0.47/0.67      (![X12 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X12)
% 0.47/0.67          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X12) @ X12))
% 0.47/0.67              = (k2_relat_1 @ X12))
% 0.47/0.67          | ~ (v1_funct_1 @ X12)
% 0.47/0.67          | ~ (v1_relat_1 @ X12))),
% 0.47/0.67      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.47/0.67  thf(t51_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.67           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 0.47/0.67               ( v2_funct_1 @ A ) ) =>
% 0.47/0.67             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.47/0.67  thf('159', plain,
% 0.47/0.67      (![X10 : $i, X11 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X10)
% 0.47/0.67          | ~ (v1_funct_1 @ X10)
% 0.47/0.67          | (r1_tarski @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X10))
% 0.47/0.67          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X11)) != (k2_relat_1 @ X11))
% 0.47/0.67          | ~ (v2_funct_1 @ X11)
% 0.47/0.67          | ~ (v1_funct_1 @ X11)
% 0.47/0.67          | ~ (v1_relat_1 @ X11))),
% 0.47/0.67      inference('cnf', [status(esa)], [t51_funct_1])).
% 0.47/0.67  thf('160', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['158', '159'])).
% 0.47/0.67  thf('161', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['160'])).
% 0.47/0.67  thf('162', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.67          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['157', '161'])).
% 0.47/0.67  thf('163', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['162'])).
% 0.47/0.67  thf('164', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['156', '163'])).
% 0.47/0.67  thf('165', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['164'])).
% 0.47/0.67  thf('166', plain,
% 0.47/0.67      (![X0 : $i, X2 : $i]:
% 0.47/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('167', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v2_funct_1 @ X0)
% 0.47/0.67          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.47/0.67          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['165', '166'])).
% 0.47/0.67  thf('168', plain,
% 0.47/0.67      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67           (k2_struct_0 @ sk_A))
% 0.47/0.67        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.47/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['155', '167'])).
% 0.47/0.67  thf('169', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['70', '71', '78'])).
% 0.47/0.67  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('173', plain,
% 0.47/0.67      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67           (k2_struct_0 @ sk_A))
% 0.47/0.67        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['168', '169', '170', '171', '172'])).
% 0.47/0.67  thf('174', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.67  thf('175', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.67         ((v5_relat_1 @ X14 @ X16)
% 0.47/0.67          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.67  thf('176', plain,
% 0.47/0.67      ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['174', '175'])).
% 0.47/0.67  thf('177', plain,
% 0.47/0.67      (![X5 : $i, X6 : $i]:
% 0.47/0.67         (~ (v5_relat_1 @ X5 @ X6)
% 0.47/0.67          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.47/0.67          | ~ (v1_relat_1 @ X5))),
% 0.47/0.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.67  thf('178', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.67        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67           (k2_struct_0 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['176', '177'])).
% 0.47/0.67  thf('179', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.67  thf('180', plain,
% 0.47/0.67      (![X3 : $i, X4 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.47/0.67          | (v1_relat_1 @ X3)
% 0.47/0.67          | ~ (v1_relat_1 @ X4))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.67  thf('181', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ 
% 0.47/0.67           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 0.47/0.67        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['179', '180'])).
% 0.47/0.67  thf('182', plain,
% 0.47/0.67      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.67  thf('183', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.67      inference('demod', [status(thm)], ['181', '182'])).
% 0.47/0.67  thf('184', plain,
% 0.47/0.67      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['178', '183'])).
% 0.47/0.67  thf('185', plain,
% 0.47/0.67      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['173', '184'])).
% 0.47/0.67  thf('186', plain,
% 0.47/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.67         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['154', '185'])).
% 0.47/0.67  thf('187', plain,
% 0.47/0.67      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67         (k1_zfmisc_1 @ 
% 0.47/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.67        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.47/0.67        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['151', '186'])).
% 0.47/0.67  thf('188', plain,
% 0.47/0.67      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.67        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67           (k1_zfmisc_1 @ 
% 0.47/0.67            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['187'])).
% 0.47/0.67  thf('189', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.67        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67           (k1_zfmisc_1 @ 
% 0.47/0.67            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['145', '188'])).
% 0.47/0.67  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('193', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 0.47/0.67  thf('194', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_C @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.47/0.67  thf(redefinition_r2_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.67         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.67       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.47/0.67  thf('195', plain,
% 0.47/0.67      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.47/0.67          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.47/0.67          | ~ (v1_funct_1 @ X25)
% 0.47/0.67          | ~ (v1_funct_1 @ X28)
% 0.47/0.67          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.47/0.67          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.47/0.67          | ((X25) = (X28))
% 0.47/0.67          | ~ (r2_funct_2 @ X26 @ X27 @ X25 @ X28))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.47/0.67  thf('196', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67             X0)
% 0.47/0.67          | ((sk_C) = (X0))
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.67               (k1_zfmisc_1 @ 
% 0.47/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.67          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.67          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['194', '195'])).
% 0.47/0.67  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('198', plain,
% 0.47/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.67  thf('199', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67             X0)
% 0.47/0.67          | ((sk_C) = (X0))
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.67               (k1_zfmisc_1 @ 
% 0.47/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.67          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67          | ~ (v1_funct_1 @ X0))),
% 0.47/0.67      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.47/0.67  thf('200', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['63', '79'])).
% 0.47/0.67  thf('201', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['63', '79'])).
% 0.47/0.67  thf('202', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.67      inference('demod', [status(thm)], ['63', '79'])).
% 0.47/0.67  thf('203', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67             X0)
% 0.47/0.67          | ((sk_C) = (X0))
% 0.47/0.67          | ~ (m1_subset_1 @ X0 @ 
% 0.47/0.67               (k1_zfmisc_1 @ 
% 0.47/0.67                (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.67          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67          | ~ (v1_funct_1 @ X0))),
% 0.47/0.67      inference('demod', [status(thm)], ['199', '200', '201', '202'])).
% 0.47/0.67  thf('204', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.67        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.67             (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.67        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.67        | ~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.67             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['193', '203'])).
% 0.47/0.67  thf('205', plain,
% 0.47/0.67      (![X9 : $i]:
% 0.47/0.67         ((v2_funct_1 @ (k2_funct_1 @ X9))
% 0.47/0.67          | ~ (v2_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_funct_1 @ X9)
% 0.47/0.67          | ~ (v1_relat_1 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.47/0.67  thf('206', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.67  thf('207', plain,
% 0.47/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X29)
% 0.47/0.67          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.47/0.67          | (v1_funct_1 @ (k2_funct_1 @ X29))
% 0.47/0.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.47/0.67          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.47/0.67          | ~ (v1_funct_1 @ X29))),
% 0.47/0.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.67  thf('208', plain,
% 0.47/0.67      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.67        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.67             (k2_struct_0 @ sk_A))
% 0.47/0.67        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['206', '207'])).
% 0.47/0.68  thf('209', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.68      inference('simplify', [status(thm)], ['133'])).
% 0.47/0.68  thf('210', plain,
% 0.47/0.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.68        (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('simplify', [status(thm)], ['142'])).
% 0.47/0.68  thf('211', plain,
% 0.47/0.68      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['208', '209', '210'])).
% 0.47/0.68  thf('212', plain,
% 0.47/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['154', '185'])).
% 0.47/0.68  thf('213', plain,
% 0.47/0.68      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.68        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['211', '212'])).
% 0.47/0.68  thf('214', plain,
% 0.47/0.68      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.47/0.68      inference('simplify', [status(thm)], ['213'])).
% 0.47/0.68  thf('215', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.68        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['205', '214'])).
% 0.47/0.68  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.68  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('219', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['215', '216', '217', '218'])).
% 0.47/0.68  thf('220', plain,
% 0.47/0.68      (![X9 : $i]:
% 0.47/0.68         ((v2_funct_1 @ (k2_funct_1 @ X9))
% 0.47/0.68          | ~ (v2_funct_1 @ X9)
% 0.47/0.68          | ~ (v1_funct_1 @ X9)
% 0.47/0.68          | ~ (v1_relat_1 @ X9))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.47/0.68  thf('221', plain,
% 0.47/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.68      inference('simplify', [status(thm)], ['122'])).
% 0.47/0.68  thf('222', plain,
% 0.47/0.68      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X29)
% 0.47/0.68          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.47/0.68          | (v1_funct_2 @ (k2_funct_1 @ X29) @ X30 @ X31)
% 0.47/0.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.47/0.68          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.47/0.68          | ~ (v1_funct_1 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.68  thf('223', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.68             (k2_struct_0 @ sk_A))
% 0.47/0.68        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68           (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['221', '222'])).
% 0.47/0.68  thf('224', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.68      inference('simplify', [status(thm)], ['133'])).
% 0.47/0.68  thf('225', plain,
% 0.47/0.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.68        (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('simplify', [status(thm)], ['142'])).
% 0.47/0.68  thf('226', plain,
% 0.47/0.68      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68         (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['223', '224', '225'])).
% 0.47/0.68  thf('227', plain,
% 0.47/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['154', '185'])).
% 0.47/0.68  thf('228', plain,
% 0.47/0.68      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68         (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['226', '227'])).
% 0.47/0.68  thf('229', plain,
% 0.47/0.68      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68           (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['228'])).
% 0.47/0.68  thf('230', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.68        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68           (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['220', '229'])).
% 0.47/0.68  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.68  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('234', plain,
% 0.47/0.68      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68        (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['230', '231', '232', '233'])).
% 0.47/0.68  thf('235', plain,
% 0.47/0.68      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.68        | ~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.68             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.47/0.68      inference('demod', [status(thm)], ['204', '219', '234'])).
% 0.47/0.68  thf(t65_funct_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.68       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.47/0.68  thf('236', plain,
% 0.47/0.68      (![X13 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X13)
% 0.47/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 0.47/0.68          | ~ (v1_funct_1 @ X13)
% 0.47/0.68          | ~ (v1_relat_1 @ X13))),
% 0.47/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.47/0.68  thf('237', plain,
% 0.47/0.68      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 0.47/0.68  thf('238', plain,
% 0.47/0.68      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.47/0.68          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.47/0.68          | ~ (v1_funct_1 @ X25)
% 0.47/0.68          | ~ (v1_funct_1 @ X28)
% 0.47/0.68          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.47/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.47/0.68          | (r2_funct_2 @ X26 @ X27 @ X25 @ X28)
% 0.47/0.68          | ((X25) != (X28)))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.47/0.68  thf('239', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.68         ((r2_funct_2 @ X26 @ X27 @ X28 @ X28)
% 0.47/0.68          | ~ (v1_funct_1 @ X28)
% 0.47/0.68          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.47/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.47/0.68      inference('simplify', [status(thm)], ['238'])).
% 0.47/0.68  thf('240', plain,
% 0.47/0.68      ((~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68           (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.68        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.68           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68           (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['237', '239'])).
% 0.47/0.68  thf('241', plain,
% 0.47/0.68      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68        (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['230', '231', '232', '233'])).
% 0.47/0.68  thf('242', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['215', '216', '217', '218'])).
% 0.47/0.68  thf('243', plain,
% 0.47/0.68      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.68        (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['240', '241', '242'])).
% 0.47/0.68  thf('244', plain,
% 0.47/0.68      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.68         (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.68      inference('sup+', [status(thm)], ['236', '243'])).
% 0.47/0.68  thf('245', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.68  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('247', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('248', plain,
% 0.47/0.68      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.68        (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['244', '245', '246', '247'])).
% 0.47/0.68  thf('249', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['235', '248'])).
% 0.47/0.68  thf('250', plain,
% 0.47/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['154', '185'])).
% 0.47/0.68  thf('251', plain,
% 0.47/0.68      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.47/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['144', '249', '250'])).
% 0.47/0.68  thf('252', plain,
% 0.47/0.68      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['251'])).
% 0.47/0.68  thf('253', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.68        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['114', '252'])).
% 0.47/0.68  thf('254', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.68  thf('255', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('256', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('257', plain,
% 0.47/0.68      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['253', '254', '255', '256'])).
% 0.47/0.68  thf('258', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['86', '87'])).
% 0.47/0.68  thf('259', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.68         ((r2_funct_2 @ X26 @ X27 @ X28 @ X28)
% 0.47/0.68          | ~ (v1_funct_1 @ X28)
% 0.47/0.68          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.47/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.47/0.68      inference('simplify', [status(thm)], ['238'])).
% 0.47/0.68  thf('260', plain,
% 0.47/0.68      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.68           sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['258', '259'])).
% 0.47/0.68  thf('261', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('263', plain,
% 0.47/0.68      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['260', '261', '262'])).
% 0.47/0.68  thf('264', plain, ($false),
% 0.47/0.68      inference('demod', [status(thm)], ['113', '257', '263'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
