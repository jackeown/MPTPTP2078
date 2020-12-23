%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GndV7CWUcf

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:57 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  327 (18585 expanded)
%              Number of leaves         :   49 (5377 expanded)
%              Depth                    :   33
%              Number of atoms          : 2854 (444815 expanded)
%              Number of equality atoms :  198 (23259 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( v1_partfun1 @ X40 @ X41 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X40 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('40',plain,(
    ! [X52: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 )
      | ( v2_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['38','45'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('47',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_partfun1 @ X47 @ X46 )
      | ( ( k1_relat_1 @ X47 )
        = X46 )
      | ~ ( v4_relat_1 @ X47 @ X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','57'])).

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

thf('59',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X50 @ X49 @ X48 )
       != X49 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['38','45'])).

thf('75',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_partfun1 @ X47 @ X46 )
      | ( ( k1_relat_1 @ X47 )
        = X46 )
      | ~ ( v4_relat_1 @ X47 @ X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('81',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('87',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','88'])).

thf('90',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('93',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','56'])).

thf('95',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','61','89','95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('100',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('103',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('104',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('107',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('110',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['105','110'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('112',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('113',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('115',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('118',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('120',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['32'])).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k9_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('132',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('134',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','132','133'])).

thf('135',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','134'])).

thf('136',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['136'])).

thf('138',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','56'])).

thf('140',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','56'])).

thf('141',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','57'])).

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

thf('143',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k2_relset_1 @ X54 @ X53 @ X55 )
       != X53 )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_tops_2 @ X54 @ X53 @ X55 )
        = ( k2_funct_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X54 @ X53 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('144',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','88'])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('149',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','145','146','147','148'])).

thf('150',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf('152',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','150','151'])).

thf('153',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('154',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( v1_partfun1 @ X40 @ X41 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X40 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','57'])).

thf('157',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X50 @ X49 @ X48 )
       != X49 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('158',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','88'])).

thf('161',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('162',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','159','160','161','162'])).

thf('164',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','57'])).

thf('166',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X50 @ X49 @ X48 )
       != X49 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X48 ) @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('167',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','88'])).

thf('170',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171'])).

thf('173',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','164','173'])).

thf('175',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_partfun1 @ X47 @ X46 )
      | ( ( k1_relat_1 @ X47 )
        = X46 )
      | ~ ( v4_relat_1 @ X47 @ X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('176',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('178',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('179',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('180',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('181',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('183',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('184',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['181','186'])).

thf('188',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['180'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('191',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['180'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('194',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_relset_1 @ X0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['192','195'])).

thf('197',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['180'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('199',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['189','200'])).

thf('202',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('203',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['203','206'])).

thf('208',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('209',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['201','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        = ( k2_relat_1 @ sk_C ) )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','210'])).

thf('212',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('213',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('214',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('219',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('220',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['218','219'])).

thf('221',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('224',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['217','224'])).

thf('226',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf('227',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ( r1_tarski @ sk_C @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['212','227'])).

thf('229',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('230',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
    | ( k1_xboole_0 = sk_C ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ( k1_xboole_0 = sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','230'])).

thf('232',plain,
    ( ( k1_xboole_0 = sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('234',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('235',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['149'])).

thf('237',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','33','34'])).

thf('238',plain,(
    ! [X51: $i] :
      ( ( ( k2_struct_0 @ X51 )
        = ( u1_struct_0 @ X51 ) )
      | ~ ( l1_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('239',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['136'])).

thf('240',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['237','242'])).

thf('244',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','33','34'])).

thf('245',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('247',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','56'])).

thf('248',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','87'])).

thf('249',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('250',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('251',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['245','246','247','248','249','250'])).

thf('252',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['236','251'])).

thf('253',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['235','252'])).

thf('254',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ( k1_xboole_0 = sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['232','253'])).

thf('255',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('257',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('259',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['189','200'])).

thf('260',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['235','252'])).

thf('262',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('265',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('266',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['264','267'])).

thf('269',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['235','252'])).

thf('270',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['270'])).

thf('272',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['257','263','271'])).

thf('273',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['136'])).

thf('274',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['272','273'])).

thf('275',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['152','274'])).

thf('276',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['135','275'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GndV7CWUcf
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 1639 iterations in 0.433s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.68/0.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.68/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.89  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.68/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.68/0.89  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.68/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.89  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.68/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.89  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.68/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.89  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.68/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.68/0.89  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.68/0.89  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.68/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.89  thf(d3_struct_0, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.68/0.89  thf('0', plain,
% 0.68/0.89      (![X51 : $i]:
% 0.68/0.89         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.89  thf(t62_tops_2, conjecture,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( l1_struct_0 @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.68/0.89           ( ![C:$i]:
% 0.68/0.89             ( ( ( v1_funct_1 @ C ) & 
% 0.68/0.89                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.68/0.89                 ( m1_subset_1 @
% 0.68/0.89                   C @ 
% 0.68/0.89                   ( k1_zfmisc_1 @
% 0.68/0.89                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.68/0.89               ( ( ( ( k2_relset_1 @
% 0.68/0.89                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.68/0.89                     ( k2_struct_0 @ B ) ) & 
% 0.68/0.89                   ( v2_funct_1 @ C ) ) =>
% 0.68/0.89                 ( ( ( k1_relset_1 @
% 0.68/0.89                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.68/0.89                       ( k2_tops_2 @
% 0.68/0.89                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.68/0.89                     ( k2_struct_0 @ B ) ) & 
% 0.68/0.89                   ( ( k2_relset_1 @
% 0.68/0.89                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.68/0.89                       ( k2_tops_2 @
% 0.68/0.89                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.68/0.89                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.89    (~( ![A:$i]:
% 0.68/0.89        ( ( l1_struct_0 @ A ) =>
% 0.68/0.89          ( ![B:$i]:
% 0.68/0.89            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.68/0.89              ( ![C:$i]:
% 0.68/0.89                ( ( ( v1_funct_1 @ C ) & 
% 0.68/0.89                    ( v1_funct_2 @
% 0.68/0.89                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.68/0.89                    ( m1_subset_1 @
% 0.68/0.89                      C @ 
% 0.68/0.89                      ( k1_zfmisc_1 @
% 0.68/0.89                        ( k2_zfmisc_1 @
% 0.68/0.89                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.68/0.89                  ( ( ( ( k2_relset_1 @
% 0.68/0.89                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.68/0.89                        ( k2_struct_0 @ B ) ) & 
% 0.68/0.89                      ( v2_funct_1 @ C ) ) =>
% 0.68/0.89                    ( ( ( k1_relset_1 @
% 0.68/0.89                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.68/0.89                          ( k2_tops_2 @
% 0.68/0.89                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.68/0.89                        ( k2_struct_0 @ B ) ) & 
% 0.68/0.89                      ( ( k2_relset_1 @
% 0.68/0.89                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.68/0.89                          ( k2_tops_2 @
% 0.68/0.89                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.68/0.89                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.68/0.89  thf('1', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C @ 
% 0.68/0.89        (k1_zfmisc_1 @ 
% 0.68/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('2', plain,
% 0.68/0.89      (((m1_subset_1 @ sk_C @ 
% 0.68/0.89         (k1_zfmisc_1 @ 
% 0.68/0.89          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.68/0.89        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.89      inference('sup+', [status(thm)], ['0', '1'])).
% 0.68/0.89  thf('3', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('4', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C @ 
% 0.68/0.89        (k1_zfmisc_1 @ 
% 0.68/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.68/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.68/0.89  thf('5', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C @ 
% 0.68/0.89        (k1_zfmisc_1 @ 
% 0.68/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.68/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.68/0.89  thf(redefinition_k2_relset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.89       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.68/0.89  thf('6', plain,
% 0.68/0.89      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.68/0.89         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.68/0.89          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.68/0.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.68/0.89  thf('7', plain,
% 0.68/0.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.89         = (k2_relat_1 @ sk_C))),
% 0.68/0.89      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.89  thf('8', plain,
% 0.68/0.89      (![X51 : $i]:
% 0.68/0.89         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.89  thf('9', plain,
% 0.68/0.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.68/0.89         = (k2_struct_0 @ sk_B))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('10', plain,
% 0.68/0.89      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.89          = (k2_struct_0 @ sk_B))
% 0.68/0.89        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.89      inference('sup+', [status(thm)], ['8', '9'])).
% 0.68/0.89  thf('11', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('12', plain,
% 0.68/0.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.89         = (k2_struct_0 @ sk_B))),
% 0.68/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.68/0.89  thf('13', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.68/0.89      inference('sup+', [status(thm)], ['7', '12'])).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C @ 
% 0.68/0.89        (k1_zfmisc_1 @ 
% 0.68/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.68/0.89      inference('demod', [status(thm)], ['4', '13'])).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C @ 
% 0.68/0.89        (k1_zfmisc_1 @ 
% 0.68/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(cc5_funct_2, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.68/0.89       ( ![C:$i]:
% 0.68/0.89         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.89           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.68/0.89             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.68/0.89         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.68/0.89          | (v1_partfun1 @ X40 @ X41)
% 0.68/0.89          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.68/0.89          | ~ (v1_funct_1 @ X40)
% 0.68/0.89          | (v1_xboole_0 @ X42))),
% 0.68/0.89      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.68/0.89  thf('17', plain,
% 0.68/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.68/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.68/0.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.68/0.89        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.89  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('20', plain,
% 0.68/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.68/0.89        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.68/0.89      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      (![X51 : $i]:
% 0.68/0.89         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.89  thf('22', plain,
% 0.68/0.89      ((m1_subset_1 @ sk_C @ 
% 0.68/0.89        (k1_zfmisc_1 @ 
% 0.68/0.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf(dt_k2_relset_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.89       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.68/0.89  thf('23', plain,
% 0.68/0.89      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.68/0.89         ((m1_subset_1 @ (k2_relset_1 @ X31 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))
% 0.68/0.89          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.68/0.89  thf('24', plain,
% 0.68/0.89      ((m1_subset_1 @ 
% 0.68/0.89        (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.68/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.89  thf('25', plain,
% 0.68/0.89      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.68/0.89         = (k2_struct_0 @ sk_B))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('26', plain,
% 0.68/0.89      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.68/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.68/0.89      inference('demod', [status(thm)], ['24', '25'])).
% 0.68/0.89  thf(t3_subset, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.89  thf('27', plain,
% 0.68/0.89      (![X9 : $i, X10 : $i]:
% 0.68/0.89         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.89  thf('28', plain, ((r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.68/0.89      inference('sup-', [status(thm)], ['26', '27'])).
% 0.68/0.89  thf(d10_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.89  thf('29', plain,
% 0.68/0.89      (![X1 : $i, X3 : $i]:
% 0.68/0.89         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.89  thf('30', plain,
% 0.68/0.89      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.68/0.89        | ((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['28', '29'])).
% 0.68/0.89  thf('31', plain,
% 0.68/0.89      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.68/0.89        | ~ (l1_struct_0 @ sk_B)
% 0.68/0.89        | ((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['21', '30'])).
% 0.68/0.89  thf('32', plain,
% 0.68/0.89      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.90  thf('33', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.68/0.90      inference('simplify', [status(thm)], ['32'])).
% 0.68/0.90  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('35', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('demod', [status(thm)], ['31', '33', '34'])).
% 0.68/0.90  thf('36', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['7', '12'])).
% 0.68/0.90  thf('37', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.90  thf('38', plain,
% 0.68/0.90      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.68/0.90        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.68/0.90      inference('demod', [status(thm)], ['20', '37'])).
% 0.68/0.90  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['7', '12'])).
% 0.68/0.90  thf(fc5_struct_0, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.68/0.90       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.68/0.90  thf('40', plain,
% 0.68/0.90      (![X52 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ (k2_struct_0 @ X52))
% 0.68/0.90          | ~ (l1_struct_0 @ X52)
% 0.68/0.90          | (v2_struct_0 @ X52))),
% 0.68/0.90      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.68/0.90  thf('41', plain,
% 0.68/0.90      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.68/0.90        | (v2_struct_0 @ sk_B)
% 0.68/0.90        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup-', [status(thm)], ['39', '40'])).
% 0.68/0.90  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('43', plain,
% 0.68/0.90      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.68/0.90      inference('demod', [status(thm)], ['41', '42'])).
% 0.68/0.90  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('45', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('clc', [status(thm)], ['43', '44'])).
% 0.68/0.90  thf('46', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('clc', [status(thm)], ['38', '45'])).
% 0.68/0.90  thf(d4_partfun1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.68/0.90       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.68/0.90  thf('47', plain,
% 0.68/0.90      (![X46 : $i, X47 : $i]:
% 0.68/0.90         (~ (v1_partfun1 @ X47 @ X46)
% 0.68/0.90          | ((k1_relat_1 @ X47) = (X46))
% 0.68/0.90          | ~ (v4_relat_1 @ X47 @ X46)
% 0.68/0.90          | ~ (v1_relat_1 @ X47))),
% 0.68/0.90      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.68/0.90  thf('48', plain,
% 0.68/0.90      ((~ (v1_relat_1 @ sk_C)
% 0.68/0.90        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.68/0.90        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['46', '47'])).
% 0.68/0.90  thf('49', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(cc2_relat_1, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( v1_relat_1 @ A ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.68/0.90  thf('50', plain,
% 0.68/0.90      (![X12 : $i, X13 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.68/0.90          | (v1_relat_1 @ X12)
% 0.68/0.90          | ~ (v1_relat_1 @ X13))),
% 0.68/0.90      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.68/0.90  thf('51', plain,
% 0.68/0.90      ((~ (v1_relat_1 @ 
% 0.68/0.90           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.68/0.90        | (v1_relat_1 @ sk_C))),
% 0.68/0.90      inference('sup-', [status(thm)], ['49', '50'])).
% 0.68/0.90  thf(fc6_relat_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.68/0.90  thf('52', plain,
% 0.68/0.90      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.68/0.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.68/0.90  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['51', '52'])).
% 0.68/0.90  thf('54', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(cc2_relset_1, axiom,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.90       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.68/0.90  thf('55', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.90         ((v4_relat_1 @ X22 @ X23)
% 0.68/0.90          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.68/0.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.68/0.90  thf('56', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('sup-', [status(thm)], ['54', '55'])).
% 0.68/0.90  thf('57', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['48', '53', '56'])).
% 0.68/0.90  thf('58', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.68/0.90      inference('demod', [status(thm)], ['14', '57'])).
% 0.68/0.90  thf(t31_funct_2, axiom,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.90       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.68/0.90         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.68/0.90           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.68/0.90           ( m1_subset_1 @
% 0.68/0.90             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.68/0.90  thf('59', plain,
% 0.68/0.90      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.68/0.90         (~ (v2_funct_1 @ X48)
% 0.68/0.90          | ((k2_relset_1 @ X50 @ X49 @ X48) != (X49))
% 0.68/0.90          | (m1_subset_1 @ (k2_funct_1 @ X48) @ 
% 0.68/0.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.68/0.90          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.68/0.90          | ~ (v1_funct_2 @ X48 @ X50 @ X49)
% 0.68/0.90          | ~ (v1_funct_1 @ X48))),
% 0.68/0.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.68/0.90  thf('60', plain,
% 0.68/0.90      ((~ (v1_funct_1 @ sk_C)
% 0.68/0.90        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.68/0.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.68/0.90           (k1_zfmisc_1 @ 
% 0.68/0.90            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.68/0.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90            != (k2_relat_1 @ sk_C))
% 0.68/0.90        | ~ (v2_funct_1 @ sk_C))),
% 0.68/0.90      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.90  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('62', plain,
% 0.68/0.90      (![X51 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('63', plain,
% 0.68/0.90      (![X51 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('64', plain,
% 0.68/0.90      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('65', plain,
% 0.68/0.90      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.68/0.90        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.90      inference('sup+', [status(thm)], ['63', '64'])).
% 0.68/0.90  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('67', plain,
% 0.68/0.90      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.68/0.90      inference('demod', [status(thm)], ['65', '66'])).
% 0.68/0.90  thf('68', plain,
% 0.68/0.90      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.68/0.90        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['62', '67'])).
% 0.68/0.90  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('70', plain,
% 0.68/0.90      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('demod', [status(thm)], ['68', '69'])).
% 0.68/0.90  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['7', '12'])).
% 0.68/0.90  thf('72', plain,
% 0.68/0.90      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['70', '71'])).
% 0.68/0.90  thf('73', plain,
% 0.68/0.90      (![X51 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('74', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('clc', [status(thm)], ['38', '45'])).
% 0.68/0.90  thf('75', plain,
% 0.68/0.90      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.90      inference('sup+', [status(thm)], ['73', '74'])).
% 0.68/0.90  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('77', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['75', '76'])).
% 0.68/0.90  thf('78', plain,
% 0.68/0.90      (![X46 : $i, X47 : $i]:
% 0.68/0.90         (~ (v1_partfun1 @ X47 @ X46)
% 0.68/0.90          | ((k1_relat_1 @ X47) = (X46))
% 0.68/0.90          | ~ (v4_relat_1 @ X47 @ X46)
% 0.68/0.90          | ~ (v1_relat_1 @ X47))),
% 0.68/0.90      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.68/0.90  thf('79', plain,
% 0.68/0.90      ((~ (v1_relat_1 @ sk_C)
% 0.68/0.90        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.68/0.90        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['77', '78'])).
% 0.68/0.90  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['51', '52'])).
% 0.68/0.90  thf('81', plain,
% 0.68/0.90      (![X51 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('82', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('83', plain,
% 0.68/0.90      (((m1_subset_1 @ sk_C @ 
% 0.68/0.90         (k1_zfmisc_1 @ 
% 0.68/0.90          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.68/0.90        | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.90      inference('sup+', [status(thm)], ['81', '82'])).
% 0.68/0.90  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('85', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.90      inference('demod', [status(thm)], ['83', '84'])).
% 0.68/0.90  thf('86', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.90         ((v4_relat_1 @ X22 @ X23)
% 0.68/0.90          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.68/0.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.68/0.90  thf('87', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.68/0.90      inference('sup-', [status(thm)], ['85', '86'])).
% 0.68/0.90  thf('88', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['79', '80', '87'])).
% 0.68/0.90  thf('89', plain,
% 0.68/0.90      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['72', '88'])).
% 0.68/0.90  thf('90', plain,
% 0.68/0.90      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.68/0.90         = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('demod', [status(thm)], ['10', '11'])).
% 0.68/0.90  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['7', '12'])).
% 0.68/0.90  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['7', '12'])).
% 0.68/0.90  thf('93', plain,
% 0.68/0.90      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90         = (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.68/0.90  thf('94', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['48', '53', '56'])).
% 0.68/0.90  thf('95', plain,
% 0.68/0.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90         = (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['93', '94'])).
% 0.68/0.90  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('97', plain,
% 0.68/0.90      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.68/0.90         (k1_zfmisc_1 @ 
% 0.68/0.90          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.68/0.90        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['60', '61', '89', '95', '96'])).
% 0.68/0.90  thf('98', plain,
% 0.68/0.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['97'])).
% 0.68/0.90  thf('99', plain,
% 0.68/0.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.68/0.90         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.68/0.90          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.68/0.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.68/0.90  thf('100', plain,
% 0.68/0.90      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.68/0.90         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['98', '99'])).
% 0.68/0.90  thf('101', plain,
% 0.68/0.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['97'])).
% 0.68/0.90  thf('102', plain,
% 0.68/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.90         ((v4_relat_1 @ X22 @ X23)
% 0.68/0.90          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.68/0.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.68/0.90  thf('103', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('sup-', [status(thm)], ['101', '102'])).
% 0.68/0.90  thf(t209_relat_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.68/0.90       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.68/0.90  thf('104', plain,
% 0.68/0.90      (![X18 : $i, X19 : $i]:
% 0.68/0.90         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.68/0.90          | ~ (v4_relat_1 @ X18 @ X19)
% 0.68/0.90          | ~ (v1_relat_1 @ X18))),
% 0.68/0.90      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.68/0.90  thf('105', plain,
% 0.68/0.90      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.68/0.90        | ((k2_funct_1 @ sk_C)
% 0.68/0.90            = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['103', '104'])).
% 0.68/0.90  thf('106', plain,
% 0.68/0.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['97'])).
% 0.68/0.90  thf('107', plain,
% 0.68/0.90      (![X12 : $i, X13 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.68/0.90          | (v1_relat_1 @ X12)
% 0.68/0.90          | ~ (v1_relat_1 @ X13))),
% 0.68/0.90      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.68/0.90  thf('108', plain,
% 0.68/0.90      ((~ (v1_relat_1 @ 
% 0.68/0.90           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.68/0.90        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['106', '107'])).
% 0.68/0.90  thf('109', plain,
% 0.68/0.90      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.68/0.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.68/0.90  thf('110', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['108', '109'])).
% 0.68/0.90  thf('111', plain,
% 0.68/0.90      (((k2_funct_1 @ sk_C)
% 0.68/0.90         = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['105', '110'])).
% 0.68/0.90  thf(t148_relat_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( v1_relat_1 @ B ) =>
% 0.68/0.90       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.68/0.90  thf('112', plain,
% 0.68/0.90      (![X16 : $i, X17 : $i]:
% 0.68/0.90         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.68/0.90          | ~ (v1_relat_1 @ X16))),
% 0.68/0.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.90  thf('113', plain,
% 0.68/0.90      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.68/0.90          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 0.68/0.90        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.68/0.90      inference('sup+', [status(thm)], ['111', '112'])).
% 0.68/0.90  thf('114', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.68/0.90      inference('sup-', [status(thm)], ['85', '86'])).
% 0.68/0.90  thf('115', plain,
% 0.68/0.90      (![X18 : $i, X19 : $i]:
% 0.68/0.90         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.68/0.90          | ~ (v4_relat_1 @ X18 @ X19)
% 0.68/0.90          | ~ (v1_relat_1 @ X18))),
% 0.68/0.90      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.68/0.90  thf('116', plain,
% 0.68/0.90      ((~ (v1_relat_1 @ sk_C)
% 0.68/0.90        | ((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['114', '115'])).
% 0.68/0.90  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['51', '52'])).
% 0.68/0.90  thf('118', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.68/0.90      inference('demod', [status(thm)], ['116', '117'])).
% 0.68/0.90  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['51', '52'])).
% 0.68/0.90  thf('120', plain,
% 0.68/0.90      (![X16 : $i, X17 : $i]:
% 0.68/0.90         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.68/0.90          | ~ (v1_relat_1 @ X16))),
% 0.68/0.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.90  thf('121', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['119', '120'])).
% 0.68/0.90  thf('122', plain,
% 0.68/0.90      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.68/0.90      inference('sup+', [status(thm)], ['118', '121'])).
% 0.68/0.90  thf('123', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['79', '80', '87'])).
% 0.68/0.90  thf('124', plain,
% 0.68/0.90      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['122', '123'])).
% 0.68/0.90  thf('125', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.68/0.90      inference('simplify', [status(thm)], ['32'])).
% 0.68/0.90  thf(t177_funct_1, axiom,
% 0.68/0.90    (![A:$i]:
% 0.68/0.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.90       ( ![B:$i]:
% 0.68/0.90         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.68/0.90           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.68/0.90             ( B ) ) ) ) ))).
% 0.68/0.90  thf('126', plain,
% 0.68/0.90      (![X20 : $i, X21 : $i]:
% 0.68/0.90         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.68/0.90          | ((k9_relat_1 @ (k2_funct_1 @ X21) @ (k9_relat_1 @ X21 @ X20))
% 0.68/0.90              = (X20))
% 0.68/0.90          | ~ (v2_funct_1 @ X21)
% 0.68/0.90          | ~ (v1_funct_1 @ X21)
% 0.68/0.90          | ~ (v1_relat_1 @ X21))),
% 0.68/0.90      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.68/0.90  thf('127', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (v1_relat_1 @ X0)
% 0.68/0.90          | ~ (v1_funct_1 @ X0)
% 0.68/0.90          | ~ (v2_funct_1 @ X0)
% 0.68/0.90          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.68/0.90              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['125', '126'])).
% 0.68/0.90  thf('128', plain,
% 0.68/0.90      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.68/0.90          = (k1_relat_1 @ sk_C))
% 0.68/0.90        | ~ (v2_funct_1 @ sk_C)
% 0.68/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.68/0.90        | ~ (v1_relat_1 @ sk_C))),
% 0.68/0.90      inference('sup+', [status(thm)], ['124', '127'])).
% 0.68/0.90  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.90      inference('demod', [status(thm)], ['51', '52'])).
% 0.68/0.90  thf('132', plain,
% 0.68/0.90      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.68/0.90         = (k1_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 0.68/0.90  thf('133', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['108', '109'])).
% 0.68/0.90  thf('134', plain,
% 0.68/0.90      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['113', '132', '133'])).
% 0.68/0.90  thf('135', plain,
% 0.68/0.90      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.68/0.90         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['100', '134'])).
% 0.68/0.90  thf('136', plain,
% 0.68/0.90      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          != (k2_struct_0 @ sk_B))
% 0.68/0.90        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90            != (k2_struct_0 @ sk_A)))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('137', plain,
% 0.68/0.90      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          != (k2_struct_0 @ sk_A)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_A))))),
% 0.68/0.90      inference('split', [status(esa)], ['136'])).
% 0.68/0.90  thf('138', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.90  thf('139', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['48', '53', '56'])).
% 0.68/0.90  thf('140', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['48', '53', '56'])).
% 0.68/0.90  thf('141', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.90  thf('142', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.68/0.90      inference('demod', [status(thm)], ['14', '57'])).
% 0.68/0.90  thf(d4_tops_2, axiom,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.90       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.68/0.90         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.68/0.90  thf('143', plain,
% 0.68/0.90      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.68/0.90         (((k2_relset_1 @ X54 @ X53 @ X55) != (X53))
% 0.68/0.90          | ~ (v2_funct_1 @ X55)
% 0.68/0.90          | ((k2_tops_2 @ X54 @ X53 @ X55) = (k2_funct_1 @ X55))
% 0.68/0.90          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53)))
% 0.68/0.90          | ~ (v1_funct_2 @ X55 @ X54 @ X53)
% 0.68/0.90          | ~ (v1_funct_1 @ X55))),
% 0.68/0.90      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.68/0.90  thf('144', plain,
% 0.68/0.90      ((~ (v1_funct_1 @ sk_C)
% 0.68/0.90        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.68/0.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90            = (k2_funct_1 @ sk_C))
% 0.68/0.90        | ~ (v2_funct_1 @ sk_C)
% 0.68/0.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90            != (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['142', '143'])).
% 0.68/0.90  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('146', plain,
% 0.68/0.90      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['72', '88'])).
% 0.68/0.90  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('148', plain,
% 0.68/0.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90         = (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['93', '94'])).
% 0.68/0.90  thf('149', plain,
% 0.68/0.90      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90          = (k2_funct_1 @ sk_C))
% 0.68/0.90        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['144', '145', '146', '147', '148'])).
% 0.68/0.90  thf('150', plain,
% 0.68/0.90      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90         = (k2_funct_1 @ sk_C))),
% 0.68/0.90      inference('simplify', [status(thm)], ['149'])).
% 0.68/0.90  thf('151', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['79', '80', '87'])).
% 0.68/0.90  thf('152', plain,
% 0.68/0.90      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.68/0.90          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_A))))),
% 0.68/0.90      inference('demod', [status(thm)],
% 0.68/0.90                ['137', '138', '139', '140', '141', '150', '151'])).
% 0.68/0.90  thf('153', plain,
% 0.68/0.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['97'])).
% 0.68/0.90  thf('154', plain,
% 0.68/0.90      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.68/0.90          | (v1_partfun1 @ X40 @ X41)
% 0.68/0.90          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.68/0.90          | ~ (v1_funct_1 @ X40)
% 0.68/0.90          | (v1_xboole_0 @ X42))),
% 0.68/0.90      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.68/0.90  thf('155', plain,
% 0.68/0.90      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.68/0.90        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.68/0.90        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.68/0.90             (k1_relat_1 @ sk_C))
% 0.68/0.90        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['153', '154'])).
% 0.68/0.90  thf('156', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.68/0.90      inference('demod', [status(thm)], ['14', '57'])).
% 0.68/0.90  thf('157', plain,
% 0.68/0.90      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.68/0.90         (~ (v2_funct_1 @ X48)
% 0.68/0.90          | ((k2_relset_1 @ X50 @ X49 @ X48) != (X49))
% 0.68/0.90          | (v1_funct_1 @ (k2_funct_1 @ X48))
% 0.68/0.90          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.68/0.90          | ~ (v1_funct_2 @ X48 @ X50 @ X49)
% 0.68/0.90          | ~ (v1_funct_1 @ X48))),
% 0.68/0.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.68/0.90  thf('158', plain,
% 0.68/0.90      ((~ (v1_funct_1 @ sk_C)
% 0.68/0.90        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.68/0.90        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.68/0.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90            != (k2_relat_1 @ sk_C))
% 0.68/0.90        | ~ (v2_funct_1 @ sk_C))),
% 0.68/0.90      inference('sup-', [status(thm)], ['156', '157'])).
% 0.68/0.90  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('160', plain,
% 0.68/0.90      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['72', '88'])).
% 0.68/0.90  thf('161', plain,
% 0.68/0.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90         = (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['93', '94'])).
% 0.68/0.90  thf('162', plain, ((v2_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('163', plain,
% 0.68/0.90      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.68/0.90        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['158', '159', '160', '161', '162'])).
% 0.68/0.90  thf('164', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.68/0.90      inference('simplify', [status(thm)], ['163'])).
% 0.68/0.90  thf('165', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.68/0.90      inference('demod', [status(thm)], ['14', '57'])).
% 0.68/0.90  thf('166', plain,
% 0.68/0.90      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.68/0.90         (~ (v2_funct_1 @ X48)
% 0.68/0.90          | ((k2_relset_1 @ X50 @ X49 @ X48) != (X49))
% 0.68/0.90          | (v1_funct_2 @ (k2_funct_1 @ X48) @ X49 @ X50)
% 0.68/0.90          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.68/0.90          | ~ (v1_funct_2 @ X48 @ X50 @ X49)
% 0.68/0.90          | ~ (v1_funct_1 @ X48))),
% 0.68/0.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.68/0.90  thf('167', plain,
% 0.68/0.90      ((~ (v1_funct_1 @ sk_C)
% 0.68/0.90        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.68/0.90        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.68/0.90           (k1_relat_1 @ sk_C))
% 0.68/0.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90            != (k2_relat_1 @ sk_C))
% 0.68/0.90        | ~ (v2_funct_1 @ sk_C))),
% 0.68/0.90      inference('sup-', [status(thm)], ['165', '166'])).
% 0.68/0.90  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('169', plain,
% 0.68/0.90      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['72', '88'])).
% 0.68/0.90  thf('170', plain,
% 0.68/0.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90         = (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['93', '94'])).
% 0.68/0.90  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('172', plain,
% 0.68/0.90      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.68/0.90         (k1_relat_1 @ sk_C))
% 0.68/0.90        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['167', '168', '169', '170', '171'])).
% 0.68/0.90  thf('173', plain,
% 0.68/0.90      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.68/0.90        (k1_relat_1 @ sk_C))),
% 0.68/0.90      inference('simplify', [status(thm)], ['172'])).
% 0.68/0.90  thf('174', plain,
% 0.68/0.90      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.68/0.90        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['155', '164', '173'])).
% 0.68/0.90  thf('175', plain,
% 0.68/0.90      (![X46 : $i, X47 : $i]:
% 0.68/0.90         (~ (v1_partfun1 @ X47 @ X46)
% 0.68/0.90          | ((k1_relat_1 @ X47) = (X46))
% 0.68/0.90          | ~ (v4_relat_1 @ X47 @ X46)
% 0.68/0.90          | ~ (v1_relat_1 @ X47))),
% 0.68/0.90      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.68/0.90  thf('176', plain,
% 0.68/0.90      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.68/0.90        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.68/0.90        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.68/0.90        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['174', '175'])).
% 0.68/0.90  thf('177', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.68/0.90      inference('demod', [status(thm)], ['108', '109'])).
% 0.68/0.90  thf('178', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('sup-', [status(thm)], ['101', '102'])).
% 0.68/0.90  thf('179', plain,
% 0.68/0.90      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.68/0.90        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.68/0.90  thf(t113_zfmisc_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.68/0.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.68/0.90  thf('180', plain,
% 0.68/0.90      (![X5 : $i, X6 : $i]:
% 0.68/0.90         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.68/0.90  thf('181', plain,
% 0.68/0.90      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['180'])).
% 0.68/0.90  thf('182', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.68/0.90      inference('simplify', [status(thm)], ['32'])).
% 0.68/0.90  thf('183', plain,
% 0.68/0.90      (![X9 : $i, X11 : $i]:
% 0.68/0.90         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.68/0.90      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.90  thf('184', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['182', '183'])).
% 0.68/0.90  thf('185', plain,
% 0.68/0.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.68/0.90         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.68/0.90          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.68/0.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.68/0.90  thf('186', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((k2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.68/0.90           = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['184', '185'])).
% 0.68/0.90  thf('187', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.68/0.90           = (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 0.68/0.90      inference('sup+', [status(thm)], ['181', '186'])).
% 0.68/0.90  thf('188', plain,
% 0.68/0.90      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['180'])).
% 0.68/0.90  thf('189', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         ((k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.68/0.90           = (k2_relat_1 @ k1_xboole_0))),
% 0.68/0.90      inference('demod', [status(thm)], ['187', '188'])).
% 0.68/0.90  thf('190', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['182', '183'])).
% 0.68/0.90  thf('191', plain,
% 0.68/0.90      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.68/0.90         ((m1_subset_1 @ (k2_relset_1 @ X31 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))
% 0.68/0.90          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.68/0.90      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.68/0.90  thf('192', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (m1_subset_1 @ (k2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 0.68/0.90          (k1_zfmisc_1 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['190', '191'])).
% 0.68/0.90  thf('193', plain,
% 0.68/0.90      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['180'])).
% 0.68/0.90  thf(cc3_relset_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( v1_xboole_0 @ A ) =>
% 0.68/0.90       ( ![C:$i]:
% 0.68/0.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.90           ( v1_xboole_0 @ C ) ) ) ))).
% 0.68/0.90  thf('194', plain,
% 0.68/0.90      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X25)
% 0.68/0.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 0.68/0.90          | (v1_xboole_0 @ X26))),
% 0.68/0.90      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.68/0.90  thf('195', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.68/0.90          | (v1_xboole_0 @ X1)
% 0.68/0.90          | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['193', '194'])).
% 0.68/0.90  thf('196', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X1)
% 0.68/0.90          | (v1_xboole_0 @ 
% 0.68/0.90             (k2_relset_1 @ X0 @ k1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['192', '195'])).
% 0.68/0.90  thf('197', plain,
% 0.68/0.90      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['180'])).
% 0.68/0.90  thf('198', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X1)
% 0.68/0.90          | (v1_xboole_0 @ (k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.68/0.90      inference('demod', [status(thm)], ['196', '197'])).
% 0.68/0.90  thf(l13_xboole_0, axiom,
% 0.68/0.90    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.68/0.90  thf('199', plain,
% 0.68/0.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.90  thf('200', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X1)
% 0.68/0.90          | ((k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['198', '199'])).
% 0.68/0.90  thf('201', plain,
% 0.68/0.90      (![X1 : $i]:
% 0.68/0.90         (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.90      inference('sup+', [status(thm)], ['189', '200'])).
% 0.68/0.90  thf('202', plain,
% 0.68/0.90      (![X5 : $i, X6 : $i]:
% 0.68/0.90         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.68/0.90  thf('203', plain,
% 0.68/0.90      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.68/0.90      inference('simplify', [status(thm)], ['202'])).
% 0.68/0.90  thf('204', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (m1_subset_1 @ (k2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 0.68/0.90          (k1_zfmisc_1 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['190', '191'])).
% 0.68/0.90  thf('205', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((k2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.68/0.90           = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['184', '185'])).
% 0.68/0.90  thf('206', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (m1_subset_1 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 0.68/0.90          (k1_zfmisc_1 @ X0))),
% 0.68/0.90      inference('demod', [status(thm)], ['204', '205'])).
% 0.68/0.90  thf('207', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (m1_subset_1 @ (k2_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.68/0.90      inference('sup+', [status(thm)], ['203', '206'])).
% 0.68/0.90  thf('208', plain,
% 0.68/0.90      (![X9 : $i, X10 : $i]:
% 0.68/0.90         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.90  thf('209', plain,
% 0.68/0.90      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.68/0.90      inference('sup-', [status(thm)], ['207', '208'])).
% 0.68/0.90  thf('210', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.90      inference('sup+', [status(thm)], ['201', '209'])).
% 0.68/0.90  thf('211', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.68/0.90          | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['179', '210'])).
% 0.68/0.90  thf('212', plain,
% 0.68/0.90      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.68/0.90        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.68/0.90  thf('213', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['182', '183'])).
% 0.68/0.90  thf('214', plain,
% 0.68/0.90      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X25)
% 0.68/0.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 0.68/0.90          | (v1_xboole_0 @ X26))),
% 0.68/0.90      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.68/0.90  thf('215', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['213', '214'])).
% 0.68/0.90  thf('216', plain,
% 0.68/0.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.90  thf('217', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['215', '216'])).
% 0.68/0.90  thf('218', plain,
% 0.68/0.90      (![X51 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('219', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.68/0.90      inference('demod', [status(thm)], ['83', '84'])).
% 0.68/0.90  thf('220', plain,
% 0.68/0.90      (((m1_subset_1 @ sk_C @ 
% 0.68/0.90         (k1_zfmisc_1 @ 
% 0.68/0.90          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.68/0.90        | ~ (l1_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['218', '219'])).
% 0.68/0.90  thf('221', plain, ((l1_struct_0 @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('222', plain,
% 0.68/0.90      ((m1_subset_1 @ sk_C @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('demod', [status(thm)], ['220', '221'])).
% 0.68/0.90  thf('223', plain,
% 0.68/0.90      (![X9 : $i, X10 : $i]:
% 0.68/0.90         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.90  thf('224', plain,
% 0.68/0.90      ((r1_tarski @ sk_C @ 
% 0.68/0.90        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['222', '223'])).
% 0.68/0.90  thf('225', plain,
% 0.68/0.90      (((r1_tarski @ sk_C @ k1_xboole_0)
% 0.68/0.90        | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.68/0.90      inference('sup+', [status(thm)], ['217', '224'])).
% 0.68/0.90  thf('226', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['79', '80', '87'])).
% 0.68/0.90  thf('227', plain,
% 0.68/0.90      (((r1_tarski @ sk_C @ k1_xboole_0)
% 0.68/0.90        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['225', '226'])).
% 0.68/0.90  thf('228', plain,
% 0.68/0.90      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.68/0.90        | (r1_tarski @ sk_C @ k1_xboole_0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['212', '227'])).
% 0.68/0.90  thf('229', plain,
% 0.68/0.90      (![X1 : $i, X3 : $i]:
% 0.68/0.90         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.68/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.90  thf('230', plain,
% 0.68/0.90      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.68/0.90        | ~ (r1_tarski @ k1_xboole_0 @ sk_C)
% 0.68/0.90        | ((k1_xboole_0) = (sk_C)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['228', '229'])).
% 0.68/0.90  thf('231', plain,
% 0.68/0.90      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.68/0.90        | ((k1_xboole_0) = (sk_C))
% 0.68/0.90        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['211', '230'])).
% 0.68/0.90  thf('232', plain,
% 0.68/0.90      ((((k1_xboole_0) = (sk_C))
% 0.68/0.90        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('simplify', [status(thm)], ['231'])).
% 0.68/0.90  thf('233', plain,
% 0.68/0.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.68/0.90        (k1_zfmisc_1 @ 
% 0.68/0.90         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['97'])).
% 0.68/0.90  thf(redefinition_k1_relset_1, axiom,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.90       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.68/0.90  thf('234', plain,
% 0.68/0.90      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.68/0.90         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.68/0.90          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.68/0.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.68/0.90  thf('235', plain,
% 0.68/0.90      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.68/0.90         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['233', '234'])).
% 0.68/0.90  thf('236', plain,
% 0.68/0.90      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.68/0.90         = (k2_funct_1 @ sk_C))),
% 0.68/0.90      inference('simplify', [status(thm)], ['149'])).
% 0.68/0.90  thf('237', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('demod', [status(thm)], ['31', '33', '34'])).
% 0.68/0.90  thf('238', plain,
% 0.68/0.90      (![X51 : $i]:
% 0.68/0.90         (((k2_struct_0 @ X51) = (u1_struct_0 @ X51)) | ~ (l1_struct_0 @ X51))),
% 0.68/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.68/0.90  thf('239', plain,
% 0.68/0.90      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          != (k2_struct_0 @ sk_B)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('split', [status(esa)], ['136'])).
% 0.68/0.90  thf('240', plain,
% 0.68/0.90      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90           != (k2_struct_0 @ sk_B))
% 0.68/0.90         | ~ (l1_struct_0 @ sk_A)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['238', '239'])).
% 0.68/0.90  thf('241', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('242', plain,
% 0.68/0.90      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          != (k2_struct_0 @ sk_B)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('demod', [status(thm)], ['240', '241'])).
% 0.68/0.90  thf('243', plain,
% 0.68/0.90      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          != (k2_struct_0 @ sk_B)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['237', '242'])).
% 0.68/0.90  thf('244', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('demod', [status(thm)], ['31', '33', '34'])).
% 0.68/0.90  thf('245', plain,
% 0.68/0.90      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          != (k2_struct_0 @ sk_B)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('demod', [status(thm)], ['243', '244'])).
% 0.68/0.90  thf('246', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['7', '12'])).
% 0.68/0.90  thf('247', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['48', '53', '56'])).
% 0.68/0.90  thf('248', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['79', '80', '87'])).
% 0.68/0.90  thf('249', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['7', '12'])).
% 0.68/0.90  thf('250', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.68/0.90      inference('sup+', [status(thm)], ['7', '12'])).
% 0.68/0.90  thf('251', plain,
% 0.68/0.90      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.68/0.90          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.68/0.90          != (k2_relat_1 @ sk_C)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('demod', [status(thm)],
% 0.68/0.90                ['245', '246', '247', '248', '249', '250'])).
% 0.68/0.90  thf('252', plain,
% 0.68/0.90      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.68/0.90          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['236', '251'])).
% 0.68/0.90  thf('253', plain,
% 0.68/0.90      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['235', '252'])).
% 0.68/0.90  thf('254', plain,
% 0.68/0.90      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.68/0.90         | ((k1_xboole_0) = (sk_C))))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['232', '253'])).
% 0.68/0.90  thf('255', plain,
% 0.68/0.90      ((((k1_xboole_0) = (sk_C)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['254'])).
% 0.68/0.90  thf('256', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.68/0.90      inference('clc', [status(thm)], ['43', '44'])).
% 0.68/0.90  thf('257', plain,
% 0.68/0.90      ((~ (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['255', '256'])).
% 0.68/0.90  thf('258', plain,
% 0.68/0.90      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.68/0.90        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.68/0.90  thf('259', plain,
% 0.68/0.90      (![X1 : $i]:
% 0.68/0.90         (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.90      inference('sup+', [status(thm)], ['189', '200'])).
% 0.68/0.90  thf('260', plain,
% 0.68/0.90      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.68/0.90        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['258', '259'])).
% 0.68/0.90  thf('261', plain,
% 0.68/0.90      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['235', '252'])).
% 0.68/0.90  thf('262', plain,
% 0.68/0.90      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.68/0.90         | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['260', '261'])).
% 0.68/0.90  thf('263', plain,
% 0.68/0.90      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['262'])).
% 0.68/0.90  thf('264', plain,
% 0.68/0.90      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.68/0.90        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.68/0.90      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.68/0.90  thf('265', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['182', '183'])).
% 0.68/0.90  thf('266', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]:
% 0.68/0.90         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.68/0.90          | (v1_xboole_0 @ X1)
% 0.68/0.90          | ~ (v1_xboole_0 @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['193', '194'])).
% 0.68/0.90  thf('267', plain,
% 0.68/0.90      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['265', '266'])).
% 0.68/0.90  thf('268', plain,
% 0.68/0.90      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.68/0.90        | (v1_xboole_0 @ k1_xboole_0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['264', '267'])).
% 0.68/0.90  thf('269', plain,
% 0.68/0.90      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['235', '252'])).
% 0.68/0.90  thf('270', plain,
% 0.68/0.90      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.68/0.90         | (v1_xboole_0 @ k1_xboole_0)))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('sup-', [status(thm)], ['268', '269'])).
% 0.68/0.90  thf('271', plain,
% 0.68/0.90      (((v1_xboole_0 @ k1_xboole_0))
% 0.68/0.90         <= (~
% 0.68/0.90             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90                = (k2_struct_0 @ sk_B))))),
% 0.68/0.90      inference('simplify', [status(thm)], ['270'])).
% 0.68/0.90  thf('272', plain,
% 0.68/0.90      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          = (k2_struct_0 @ sk_B)))),
% 0.68/0.90      inference('demod', [status(thm)], ['257', '263', '271'])).
% 0.68/0.90  thf('273', plain,
% 0.68/0.90      (~
% 0.68/0.90       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          = (k2_struct_0 @ sk_A))) | 
% 0.68/0.90       ~
% 0.68/0.90       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          = (k2_struct_0 @ sk_B)))),
% 0.68/0.90      inference('split', [status(esa)], ['136'])).
% 0.68/0.90  thf('274', plain,
% 0.68/0.90      (~
% 0.68/0.90       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.68/0.90          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.68/0.90          = (k2_struct_0 @ sk_A)))),
% 0.68/0.90      inference('sat_resolution*', [status(thm)], ['272', '273'])).
% 0.68/0.90  thf('275', plain,
% 0.68/0.90      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.68/0.90         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.68/0.90      inference('simpl_trail', [status(thm)], ['152', '274'])).
% 0.68/0.90  thf('276', plain, ($false),
% 0.68/0.90      inference('simplify_reflect-', [status(thm)], ['135', '275'])).
% 0.68/0.90  
% 0.68/0.90  % SZS output end Refutation
% 0.68/0.90  
% 0.68/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
