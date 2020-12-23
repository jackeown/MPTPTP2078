%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LXnafJYV5R

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:13 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  347 (3651 expanded)
%              Number of leaves         :   47 (1102 expanded)
%              Depth                    :   40
%              Number of atoms          : 3137 (70485 expanded)
%              Number of equality atoms :  164 (2044 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
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

thf('1',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','17'])).

thf('19',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v5_relat_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','40','42','43'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X37: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','50'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('52',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','57'])).

thf('59',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','50'])).

thf('61',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('67',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('73',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','73'])).

thf('75',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','74'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','40','42','43'])).

thf('77',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','74'])).

thf('78',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','74'])).

thf('79',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','40','42','43'])).

thf('80',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','75','76','77','78','79'])).

thf('81',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

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

thf('86',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X38 @ X40 )
       != X38 )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_tops_2 @ X39 @ X38 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88','97','98','107'])).

thf('109',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['80','109'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('111',plain,(
    ! [X13: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X38 @ X40 )
       != X38 )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_tops_2 @ X39 @ X38 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('124',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('128',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129'])).

thf('131',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('133',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X32 ) @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['139'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('141',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('142',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('144',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('145',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('146',plain,(
    ! [X13: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('147',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('148',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('149',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('150',plain,(
    ! [X13: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('151',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('152',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('153',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('154',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ ( k2_relat_1 @ X35 ) ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('155',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('157',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('160',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('164',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X15 ) @ ( k9_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['153','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['152','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['151','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['150','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['149','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['146','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['143','187'])).

thf('189',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('190',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('191',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('193',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('195',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ ( k2_relat_1 @ X35 ) ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) @ ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['193','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('199',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('200',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('202',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('203',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('204',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['197','198','199','200','201','202','203'])).

thf('205',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('206',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('207',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('209',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['204','209'])).

thf('211',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('212',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('214',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('216',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('218',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('220',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('222',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('226',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223','224','225'])).

thf('227',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('228',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','73'])).

thf('230',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['188','230','231','232','233'])).

thf('235',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('236',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','236'])).

thf('238',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('239',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('240',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['237','238','239','240','241'])).

thf('243',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['141','242'])).

thf('244',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('245',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['243','244','245','246','247'])).

thf('249',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','131','140','248'])).

thf('250',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('251',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('252',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('254',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('256',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('257',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('259',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['254','259'])).

thf('261',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('262',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['260','261'])).

thf('263',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('264',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('265',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('267',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['265','266'])).

thf('268',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('269',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('270',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('272',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['267','270','271','272','273'])).

thf('275',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ ( k2_relat_1 @ X35 ) ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('276',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('277',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['274','277'])).

thf('279',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('280',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('281',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['130'])).

thf('282',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('283',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['278','279','280','281','282'])).

thf('284',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['249','283'])).

thf('285',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['111','285'])).

thf('287',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('288',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['286','287','288','289'])).

thf('291',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

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

thf('292',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_funct_2 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('293',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_funct_2 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('294',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['291','293'])).

thf('295',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('296',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['294','295','296'])).

thf('298',plain,(
    $false ),
    inference(demod,[status(thm)],['110','290','297'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LXnafJYV5R
% 0.17/0.37  % Computer   : n024.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 13:59:06 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 363 iterations in 0.164s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.66  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.66  thf(d3_struct_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf(t64_tops_2, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.66                 ( m1_subset_1 @
% 0.46/0.66                   C @ 
% 0.46/0.66                   ( k1_zfmisc_1 @
% 0.46/0.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.66               ( ( ( ( k2_relset_1 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.66                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.66                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.66                 ( r2_funct_2 @
% 0.46/0.66                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.66                   ( k2_tops_2 @
% 0.46/0.66                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                     ( k2_tops_2 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.66                   C ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( l1_struct_0 @ A ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                    ( v1_funct_2 @
% 0.46/0.66                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.66                    ( m1_subset_1 @
% 0.46/0.66                      C @ 
% 0.46/0.66                      ( k1_zfmisc_1 @
% 0.46/0.66                        ( k2_zfmisc_1 @
% 0.46/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.66                  ( ( ( ( k2_relset_1 @
% 0.46/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.66                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.66                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.66                    ( r2_funct_2 @
% 0.46/0.66                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.66                      ( k2_tops_2 @
% 0.46/0.66                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                        ( k2_tops_2 @
% 0.46/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.66                      C ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66          sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66           sk_C)
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf('3', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66          sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_C @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.66  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.66  thf(cc5_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.66       ( ![C:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.66             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.46/0.66          | (v1_partfun1 @ X23 @ X24)
% 0.46/0.66          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.46/0.66          | ~ (v1_funct_1 @ X23)
% 0.46/0.66          | (v1_xboole_0 @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.66  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('16', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['11', '12', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc2_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.66         ((v5_relat_1 @ X17 @ X19)
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('22', plain, ((v5_relat_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.66  thf(d19_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ B ) =>
% 0.46/0.66       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         (~ (v5_relat_1 @ X5 @ X6)
% 0.46/0.66          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.46/0.66          | ~ (v1_relat_1 @ X5))),
% 0.46/0.66      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc2_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.46/0.66          | (v1_relat_1 @ X3)
% 0.46/0.66          | ~ (v1_relat_1 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ 
% 0.46/0.66           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | (v1_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.66  thf(fc6_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.66  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '29'])).
% 0.46/0.66  thf(d10_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (![X0 : $i, X2 : $i]:
% 0.46/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_relat_1 @ sk_C))
% 0.46/0.66        | ((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_relat_1 @ sk_C))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.66        | ((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '32'])).
% 0.46/0.66  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_relat_1 @ sk_C))
% 0.46/0.66        | ((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.46/0.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('40', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.66      inference('simplify', [status(thm)], ['41'])).
% 0.46/0.66  thf('43', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('44', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '40', '42', '43'])).
% 0.46/0.66  thf(fc2_struct_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.66       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (u1_struct_0 @ X37))
% 0.46/0.66          | ~ (l1_struct_0 @ X37)
% 0.46/0.66          | (v2_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | (v2_struct_0 @ sk_B)
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.66  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('50', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.66  thf('51', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['18', '50'])).
% 0.46/0.66  thf(d4_partfun1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.66       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i]:
% 0.46/0.66         (~ (v1_partfun1 @ X27 @ X26)
% 0.46/0.66          | ((k1_relat_1 @ X27) = (X26))
% 0.46/0.66          | ~ (v4_relat_1 @ X27 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X27))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.66         ((v4_relat_1 @ X17 @ X18)
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('57', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.66  thf('58', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54', '57'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('60', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['18', '50'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.66  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('63', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i]:
% 0.46/0.66         (~ (v1_partfun1 @ X27 @ X26)
% 0.46/0.66          | ((k1_relat_1 @ X27) = (X26))
% 0.46/0.66          | ~ (v4_relat_1 @ X27 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X27))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.66  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_C @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['67', '68'])).
% 0.46/0.66  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.66         ((v4_relat_1 @ X17 @ X18)
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('73', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.66  thf('74', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['65', '66', '73'])).
% 0.46/0.66  thf('75', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['58', '74'])).
% 0.46/0.66  thf('76', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '40', '42', '43'])).
% 0.46/0.66  thf('77', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['58', '74'])).
% 0.46/0.66  thf('78', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['58', '74'])).
% 0.46/0.66  thf('79', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '40', '42', '43'])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66          sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['4', '75', '76', '77', '78', '79'])).
% 0.46/0.66  thf('81', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.66  thf('83', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_C @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['81', '82'])).
% 0.46/0.66  thf('84', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.66  thf(d4_tops_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.66         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.66  thf('86', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 0.46/0.66          | ~ (v2_funct_1 @ X40)
% 0.46/0.66          | ((k2_tops_2 @ X39 @ X38 @ X40) = (k2_funct_1 @ X40))
% 0.46/0.66          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.46/0.66          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.46/0.66          | ~ (v1_funct_1 @ X40))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            = (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['85', '86'])).
% 0.46/0.66  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['90', '91'])).
% 0.46/0.66  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('94', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.46/0.66  thf('95', plain,
% 0.46/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['89', '94'])).
% 0.46/0.66  thf('96', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['95', '96'])).
% 0.46/0.66  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('100', plain,
% 0.46/0.66      (![X36 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('101', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('102', plain,
% 0.46/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66          = (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['100', '101'])).
% 0.46/0.66  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('104', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['102', '103'])).
% 0.46/0.66  thf('105', plain,
% 0.46/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66          = (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['99', '104'])).
% 0.46/0.66  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('107', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['105', '106'])).
% 0.46/0.66  thf('108', plain,
% 0.46/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66          = (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['87', '88', '97', '98', '107'])).
% 0.46/0.66  thf('109', plain,
% 0.46/0.66      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['108'])).
% 0.46/0.66  thf('110', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66          sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['80', '109'])).
% 0.46/0.66  thf(fc6_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.46/0.66       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.66         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.66         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         ((v2_funct_1 @ (k2_funct_1 @ X13))
% 0.46/0.66          | ~ (v2_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('112', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.66  thf(t31_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.66         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.66           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.66           ( m1_subset_1 @
% 0.46/0.66             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('113', plain,
% 0.46/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X32)
% 0.46/0.66          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.46/0.66          | (m1_subset_1 @ (k2_funct_1 @ X32) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.46/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.66          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.46/0.66          | ~ (v1_funct_1 @ X32))),
% 0.46/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.66  thf('114', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['112', '113'])).
% 0.46/0.66  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('116', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['95', '96'])).
% 0.46/0.66  thf('117', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['105', '106'])).
% 0.46/0.66  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('119', plain,
% 0.46/0.66      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 0.46/0.66  thf('120', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['119'])).
% 0.46/0.66  thf('121', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 0.46/0.66          | ~ (v2_funct_1 @ X40)
% 0.46/0.66          | ((k2_tops_2 @ X39 @ X38 @ X40) = (k2_funct_1 @ X40))
% 0.46/0.66          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.46/0.66          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.46/0.66          | ~ (v1_funct_1 @ X40))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.66  thf('122', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66             (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['120', '121'])).
% 0.46/0.66  thf('123', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.66  thf('124', plain,
% 0.46/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X32)
% 0.46/0.66          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.46/0.66          | (v1_funct_1 @ (k2_funct_1 @ X32))
% 0.46/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.66          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.46/0.66          | ~ (v1_funct_1 @ X32))),
% 0.46/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.66  thf('125', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['123', '124'])).
% 0.46/0.66  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('127', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['95', '96'])).
% 0.46/0.66  thf('128', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['105', '106'])).
% 0.46/0.66  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('130', plain,
% 0.46/0.66      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['125', '126', '127', '128', '129'])).
% 0.46/0.66  thf('131', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['130'])).
% 0.46/0.66  thf('132', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.66  thf('133', plain,
% 0.46/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X32)
% 0.46/0.66          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.46/0.66          | (v1_funct_2 @ (k2_funct_1 @ X32) @ X33 @ X34)
% 0.46/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.66          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.46/0.66          | ~ (v1_funct_1 @ X32))),
% 0.46/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.66  thf('134', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66           (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['132', '133'])).
% 0.46/0.66  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('136', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['95', '96'])).
% 0.46/0.66  thf('137', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['105', '106'])).
% 0.46/0.66  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('139', plain,
% 0.46/0.66      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66         (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 0.46/0.66  thf('140', plain,
% 0.46/0.66      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66        (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('simplify', [status(thm)], ['139'])).
% 0.46/0.66  thf(t65_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.66  thf('141', plain,
% 0.46/0.66      (![X16 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X16)
% 0.46/0.66          | ((k2_funct_1 @ (k2_funct_1 @ X16)) = (X16))
% 0.46/0.66          | ~ (v1_funct_1 @ X16)
% 0.46/0.66          | ~ (v1_relat_1 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.66  thf('142', plain,
% 0.46/0.66      (![X16 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X16)
% 0.46/0.66          | ((k2_funct_1 @ (k2_funct_1 @ X16)) = (X16))
% 0.46/0.66          | ~ (v1_funct_1 @ X16)
% 0.46/0.66          | ~ (v1_relat_1 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.66  thf('143', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('144', plain,
% 0.46/0.66      (![X16 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X16)
% 0.46/0.66          | ((k2_funct_1 @ (k2_funct_1 @ X16)) = (X16))
% 0.46/0.66          | ~ (v1_funct_1 @ X16)
% 0.46/0.66          | ~ (v1_relat_1 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.66  thf('145', plain,
% 0.46/0.66      (![X16 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X16)
% 0.46/0.66          | ((k2_funct_1 @ (k2_funct_1 @ X16)) = (X16))
% 0.46/0.66          | ~ (v1_funct_1 @ X16)
% 0.46/0.66          | ~ (v1_relat_1 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.66  thf('146', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         ((v2_funct_1 @ (k2_funct_1 @ X13))
% 0.46/0.66          | ~ (v2_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('147', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 0.46/0.66          | ~ (v2_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('148', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.46/0.66          | ~ (v2_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('149', plain,
% 0.46/0.66      (![X16 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X16)
% 0.46/0.66          | ((k2_funct_1 @ (k2_funct_1 @ X16)) = (X16))
% 0.46/0.66          | ~ (v1_funct_1 @ X16)
% 0.46/0.66          | ~ (v1_relat_1 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.66  thf('150', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         ((v2_funct_1 @ (k2_funct_1 @ X13))
% 0.46/0.66          | ~ (v2_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('151', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 0.46/0.66          | ~ (v2_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('152', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 0.46/0.66          | ~ (v2_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('153', plain,
% 0.46/0.66      (![X16 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X16)
% 0.46/0.66          | ((k2_funct_1 @ (k2_funct_1 @ X16)) = (X16))
% 0.46/0.66          | ~ (v1_funct_1 @ X16)
% 0.46/0.66          | ~ (v1_relat_1 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.66  thf(t3_funct_2, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ( v1_funct_1 @ A ) & 
% 0.46/0.66         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.46/0.66         ( m1_subset_1 @
% 0.46/0.66           A @ 
% 0.46/0.66           ( k1_zfmisc_1 @
% 0.46/0.66             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('154', plain,
% 0.46/0.66      (![X35 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X35 @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ (k2_relat_1 @ X35))))
% 0.46/0.66          | ~ (v1_funct_1 @ X35)
% 0.46/0.66          | ~ (v1_relat_1 @ X35))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.46/0.66  thf('155', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.66         ((v4_relat_1 @ X17 @ X18)
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('156', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['154', '155'])).
% 0.46/0.66  thf(t209_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.66       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.46/0.66  thf('157', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.46/0.66          | ~ (v4_relat_1 @ X11 @ X12)
% 0.46/0.66          | ~ (v1_relat_1 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.66  thf('158', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['156', '157'])).
% 0.46/0.66  thf('159', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['158'])).
% 0.46/0.66  thf(t148_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ B ) =>
% 0.46/0.66       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.46/0.66  thf('160', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.46/0.66          | ~ (v1_relat_1 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.66  thf('161', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['159', '160'])).
% 0.46/0.66  thf('162', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['161'])).
% 0.46/0.66  thf('163', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.66      inference('simplify', [status(thm)], ['41'])).
% 0.46/0.66  thf(t177_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.66           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.46/0.66             ( B ) ) ) ) ))).
% 0.46/0.66  thf('164', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.46/0.66          | ((k9_relat_1 @ (k2_funct_1 @ X15) @ (k9_relat_1 @ X15 @ X14))
% 0.46/0.66              = (X14))
% 0.46/0.66          | ~ (v2_funct_1 @ X15)
% 0.46/0.66          | ~ (v1_funct_1 @ X15)
% 0.46/0.66          | ~ (v1_relat_1 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.46/0.66  thf('165', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.46/0.66              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['163', '164'])).
% 0.46/0.66  thf('166', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66            = (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['162', '165'])).
% 0.46/0.66  thf('167', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66              = (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['166'])).
% 0.46/0.66  thf('168', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['153', '167'])).
% 0.46/0.66  thf('169', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['152', '168'])).
% 0.46/0.66  thf('170', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['169'])).
% 0.46/0.66  thf('171', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['151', '170'])).
% 0.46/0.66  thf('172', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['171'])).
% 0.46/0.66  thf('173', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['150', '172'])).
% 0.46/0.66  thf('174', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['173'])).
% 0.46/0.66  thf('175', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['149', '174'])).
% 0.46/0.66  thf('176', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['148', '175'])).
% 0.46/0.66  thf('177', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['176'])).
% 0.46/0.66  thf('178', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['147', '177'])).
% 0.46/0.66  thf('179', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['178'])).
% 0.46/0.66  thf('180', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['146', '179'])).
% 0.46/0.66  thf('181', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['180'])).
% 0.46/0.66  thf('182', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['154', '155'])).
% 0.46/0.66  thf('183', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.66           (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['181', '182'])).
% 0.46/0.66  thf('184', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.66             (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['145', '183'])).
% 0.46/0.66  thf('185', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.66           (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['184'])).
% 0.46/0.66  thf('186', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.66             (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['144', '185'])).
% 0.46/0.66  thf('187', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.66           (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['186'])).
% 0.46/0.66  thf('188', plain,
% 0.46/0.66      (((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66         (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['143', '187'])).
% 0.46/0.66  thf('189', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.66  thf('190', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.46/0.66          | ~ (v4_relat_1 @ X11 @ X12)
% 0.46/0.66          | ~ (v1_relat_1 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.66  thf('191', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['189', '190'])).
% 0.46/0.66  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('193', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['191', '192'])).
% 0.46/0.66  thf('194', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.46/0.66          | ~ (v1_relat_1 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.66  thf('195', plain,
% 0.46/0.66      (![X35 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X35 @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ (k2_relat_1 @ X35))))
% 0.46/0.66          | ~ (v1_funct_1 @ X35)
% 0.46/0.66          | ~ (v1_relat_1 @ X35))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.46/0.66  thf('196', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.46/0.66             (k9_relat_1 @ X1 @ X0))))
% 0.46/0.66          | ~ (v1_relat_1 @ X1)
% 0.46/0.66          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['194', '195'])).
% 0.46/0.66  thf('197', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | (m1_subset_1 @ (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ 
% 0.46/0.66             (k1_relat_1 @ (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))) @ 
% 0.46/0.66             (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['193', '196'])).
% 0.46/0.66  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('199', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['191', '192'])).
% 0.46/0.66  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('202', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['191', '192'])).
% 0.46/0.66  thf('203', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['191', '192'])).
% 0.46/0.66  thf('204', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.66          (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['197', '198', '199', '200', '201', '202', '203'])).
% 0.46/0.66  thf('205', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['191', '192'])).
% 0.46/0.66  thf('206', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.46/0.66          | ~ (v1_relat_1 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.66  thf('207', plain,
% 0.46/0.66      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['205', '206'])).
% 0.46/0.66  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('209', plain,
% 0.46/0.66      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['207', '208'])).
% 0.46/0.66  thf('210', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.66      inference('demod', [status(thm)], ['204', '209'])).
% 0.46/0.66  thf('211', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.66         ((v4_relat_1 @ X17 @ X18)
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('212', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['210', '211'])).
% 0.46/0.66  thf('213', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.46/0.66          | ~ (v4_relat_1 @ X11 @ X12)
% 0.46/0.66          | ~ (v1_relat_1 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.66  thf('214', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['212', '213'])).
% 0.46/0.66  thf('215', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('216', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['214', '215'])).
% 0.46/0.66  thf('217', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.46/0.66          | ~ (v1_relat_1 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.66  thf('218', plain,
% 0.46/0.66      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['216', '217'])).
% 0.46/0.66  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('220', plain,
% 0.46/0.66      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['218', '219'])).
% 0.46/0.66  thf('221', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.46/0.66              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['163', '164'])).
% 0.46/0.66  thf('222', plain,
% 0.46/0.66      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.66          = (k1_relat_1 @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['220', '221'])).
% 0.46/0.66  thf('223', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('224', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('226', plain,
% 0.46/0.66      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.66         = (k1_relat_1 @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['222', '223', '224', '225'])).
% 0.46/0.66  thf('227', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('228', plain,
% 0.46/0.66      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.66         = (k1_relat_1 @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['226', '227'])).
% 0.46/0.66  thf('229', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['65', '66', '73'])).
% 0.46/0.66  thf('230', plain,
% 0.46/0.66      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.66         = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['228', '229'])).
% 0.46/0.66  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('234', plain,
% 0.46/0.66      ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['188', '230', '231', '232', '233'])).
% 0.46/0.66  thf('235', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.46/0.66          | ~ (v4_relat_1 @ X11 @ X12)
% 0.46/0.66          | ~ (v1_relat_1 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.66  thf('236', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66            = (k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66               (k2_struct_0 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['234', '235'])).
% 0.46/0.66  thf('237', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66            = (k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66               (k2_struct_0 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['142', '236'])).
% 0.46/0.66  thf('238', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('239', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('240', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('241', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('242', plain,
% 0.46/0.66      (((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66         = (k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66            (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['237', '238', '239', '240', '241'])).
% 0.46/0.66  thf('243', plain,
% 0.46/0.66      ((((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66          = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['141', '242'])).
% 0.46/0.66  thf('244', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['191', '192'])).
% 0.46/0.66  thf('245', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('247', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('248', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['243', '244', '245', '246', '247'])).
% 0.46/0.66  thf('249', plain,
% 0.46/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['122', '131', '140', '248'])).
% 0.46/0.66  thf('250', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['119'])).
% 0.46/0.66  thf('251', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.66         ((v4_relat_1 @ X17 @ X18)
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('252', plain,
% 0.46/0.66      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['250', '251'])).
% 0.46/0.66  thf('253', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.46/0.66          | ~ (v4_relat_1 @ X11 @ X12)
% 0.46/0.66          | ~ (v1_relat_1 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.66  thf('254', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_funct_1 @ sk_C)
% 0.46/0.66            = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['252', '253'])).
% 0.46/0.66  thf('255', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['119'])).
% 0.46/0.66  thf('256', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.46/0.66          | (v1_relat_1 @ X3)
% 0.46/0.66          | ~ (v1_relat_1 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.66  thf('257', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ 
% 0.46/0.66           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 0.46/0.66        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['255', '256'])).
% 0.46/0.66  thf('258', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.66  thf('259', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['257', '258'])).
% 0.46/0.66  thf('260', plain,
% 0.46/0.66      (((k2_funct_1 @ sk_C)
% 0.46/0.66         = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['254', '259'])).
% 0.46/0.66  thf('261', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.46/0.66          | ~ (v1_relat_1 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.66  thf('262', plain,
% 0.46/0.66      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B)))
% 0.46/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['260', '261'])).
% 0.46/0.66  thf('263', plain,
% 0.46/0.66      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.66         = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['228', '229'])).
% 0.46/0.66  thf('264', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['257', '258'])).
% 0.46/0.66  thf('265', plain,
% 0.46/0.66      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['262', '263', '264'])).
% 0.46/0.66  thf('266', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['173'])).
% 0.46/0.66  thf('267', plain,
% 0.46/0.66      ((((k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.66          = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['265', '266'])).
% 0.46/0.66  thf('268', plain,
% 0.46/0.66      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['207', '208'])).
% 0.46/0.66  thf('269', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('270', plain,
% 0.46/0.66      (((k2_struct_0 @ sk_B) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['268', '269'])).
% 0.46/0.66  thf('271', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('272', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('273', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('274', plain,
% 0.46/0.66      (((k2_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['267', '270', '271', '272', '273'])).
% 0.46/0.66  thf('275', plain,
% 0.46/0.66      (![X35 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X35 @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ (k2_relat_1 @ X35))))
% 0.46/0.66          | ~ (v1_funct_1 @ X35)
% 0.46/0.66          | ~ (v1_relat_1 @ X35))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.46/0.66  thf('276', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.46/0.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.66  thf('277', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.46/0.66              = (k2_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['275', '276'])).
% 0.46/0.66  thf('278', plain,
% 0.46/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.46/0.66          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['274', '277'])).
% 0.46/0.66  thf('279', plain,
% 0.46/0.66      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['262', '263', '264'])).
% 0.46/0.66  thf('280', plain,
% 0.46/0.66      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['262', '263', '264'])).
% 0.46/0.66  thf('281', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['130'])).
% 0.46/0.66  thf('282', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['257', '258'])).
% 0.46/0.66  thf('283', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['278', '279', '280', '281', '282'])).
% 0.46/0.66  thf('284', plain,
% 0.46/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['249', '283'])).
% 0.46/0.66  thf('285', plain,
% 0.46/0.66      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['284'])).
% 0.46/0.66  thf('286', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['111', '285'])).
% 0.46/0.66  thf('287', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('288', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('289', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('290', plain,
% 0.46/0.66      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['286', '287', '288', '289'])).
% 0.46/0.66  thf('291', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.66  thf(redefinition_r2_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.66         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.66  thf('292', plain,
% 0.46/0.66      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.46/0.66          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.46/0.66          | ~ (v1_funct_1 @ X28)
% 0.46/0.66          | ~ (v1_funct_1 @ X31)
% 0.46/0.66          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.46/0.66          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.46/0.66          | (r2_funct_2 @ X29 @ X30 @ X28 @ X31)
% 0.46/0.66          | ((X28) != (X31)))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.46/0.66  thf('293', plain,
% 0.46/0.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.66         ((r2_funct_2 @ X29 @ X30 @ X31 @ X31)
% 0.46/0.66          | ~ (v1_funct_1 @ X31)
% 0.46/0.66          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.46/0.66          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['292'])).
% 0.46/0.66  thf('294', plain,
% 0.46/0.66      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.66           sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['291', '293'])).
% 0.46/0.66  thf('295', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['95', '96'])).
% 0.46/0.66  thf('296', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('297', plain,
% 0.46/0.66      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['294', '295', '296'])).
% 0.46/0.66  thf('298', plain, ($false),
% 0.46/0.66      inference('demod', [status(thm)], ['110', '290', '297'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
