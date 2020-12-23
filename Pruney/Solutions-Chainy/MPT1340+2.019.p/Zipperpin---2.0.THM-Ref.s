%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.00fCGKIN6m

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:08 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  254 (1469 expanded)
%              Number of leaves         :   40 ( 446 expanded)
%              Depth                    :   38
%              Number of atoms          : 2305 (33126 expanded)
%              Number of equality atoms :  104 (1018 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
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

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X20 @ X18 )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_partfun1 @ X13 @ X12 )
      | ( ( k1_relat_1 @ X13 )
        = X12 )
      | ~ ( v4_relat_1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('18',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21','24'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('45',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('47',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','38','43','44','45','46'])).

thf('48',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('59',plain,(
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

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    inference('sup+',[status(thm)],['41','42'])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','61','72','73','85'])).

thf('87',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['47','87'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('91',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('95',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
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

thf('100',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('102',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('107',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('111',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('120',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('121',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('122',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('125',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('126',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('129',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('131',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('132',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('133',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('134',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != X12 )
      | ( v1_partfun1 @ X13 @ X12 )
      | ~ ( v4_relat_1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('135',plain,(
    ! [X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v4_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
      | ( v1_partfun1 @ X13 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['133','135'])).

thf('137',plain,(
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
    inference('sup-',[status(thm)],['132','136'])).

thf('138',plain,(
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
    inference('sup-',[status(thm)],['131','137'])).

thf('139',plain,(
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
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
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
    inference('sup-',[status(thm)],['130','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['129','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('144',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('145',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['142','145','146','147','148'])).

thf('150',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['127','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['126','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['125','166'])).

thf('168',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('169',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['124','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['170','171','172','173'])).

thf('175',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['123','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_partfun1 @ X13 @ X12 )
      | ( ( k1_relat_1 @ X13 )
        = X12 )
      | ~ ( v4_relat_1 @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('183',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('184',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['122','184'])).

thf('186',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('187',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['185','186','187','188','189','190'])).

thf('192',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['121','191'])).

thf('193',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','109','118','192'])).

thf('194',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['89','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('200',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['88','199'])).

thf('201',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','200'])).

thf('202',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

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

thf('203',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_funct_2 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('204',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_funct_2 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['202','204'])).

thf('206',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('207',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    $false ),
    inference(demod,[status(thm)],['201','208','209','210','211'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.00fCGKIN6m
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:02:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 286 iterations in 0.175s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.64  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(t65_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X2 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X2)
% 0.46/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | ~ (v1_relat_1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.64  thf(d3_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf(t64_tops_2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_struct_0 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                 ( m1_subset_1 @
% 0.46/0.64                   C @ 
% 0.46/0.64                   ( k1_zfmisc_1 @
% 0.46/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64               ( ( ( ( k2_relset_1 @
% 0.46/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.64                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.64                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.64                 ( r2_funct_2 @
% 0.46/0.64                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.64                   ( k2_tops_2 @
% 0.46/0.64                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.64                     ( k2_tops_2 @
% 0.46/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.64                   C ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( l1_struct_0 @ A ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.64              ( ![C:$i]:
% 0.46/0.64                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                    ( v1_funct_2 @
% 0.46/0.64                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                    ( m1_subset_1 @
% 0.46/0.64                      C @ 
% 0.46/0.64                      ( k1_zfmisc_1 @
% 0.46/0.64                        ( k2_zfmisc_1 @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64                  ( ( ( ( k2_relset_1 @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.64                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.64                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.64                    ( r2_funct_2 @
% 0.46/0.64                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.64                      ( k2_tops_2 @
% 0.46/0.64                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.64                        ( k2_tops_2 @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.64                      C ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64           sk_C)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64           sk_C)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '6'])).
% 0.46/0.64  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t132_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.64           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.64           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         (((X18) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_funct_1 @ X19)
% 0.46/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.46/0.64          | (v1_partfun1 @ X19 @ X20)
% 0.46/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.46/0.64          | ~ (v1_funct_2 @ X19 @ X20 @ X18)
% 0.46/0.64          | ~ (v1_funct_1 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         (~ (v1_funct_2 @ X19 @ X20 @ X18)
% 0.46/0.64          | (v1_partfun1 @ X19 @ X20)
% 0.46/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.46/0.64          | ~ (v1_funct_1 @ X19)
% 0.46/0.64          | ((X18) = (k1_xboole_0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '12'])).
% 0.46/0.64  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.46/0.64  thf(d4_partfun1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.64       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         (~ (v1_partfun1 @ X13 @ X12)
% 0.46/0.64          | ((k1_relat_1 @ X13) = (X12))
% 0.46/0.64          | ~ (v4_relat_1 @ X13 @ X12)
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc1_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( v1_relat_1 @ C ) ))).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.64         ((v1_relat_1 @ X3)
% 0.46/0.64          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.64  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X6 @ X7)
% 0.46/0.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('24', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['18', '21', '24'])).
% 0.46/0.64  thf(fc2_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.64       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X25 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.46/0.64          | ~ (l1_struct_0 @ X25)
% 0.46/0.64          | (v2_struct_0 @ X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.64  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.64  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.46/0.64  thf('31', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('32', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('34', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('37', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf('38', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '37'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.46/0.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('43', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('44', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '37'])).
% 0.46/0.64  thf('45', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '37'])).
% 0.46/0.64  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['9', '38', '43', '44', '45', '46'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_C @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_C @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['48', '53'])).
% 0.46/0.64  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf(d4_tops_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.64         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.46/0.64          | ~ (v2_funct_1 @ X28)
% 0.46/0.64          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.46/0.64          | ~ (v1_funct_1 @ X28))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.46/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64            = (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64            != (k2_relat_1 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.64  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['62', '67'])).
% 0.46/0.64  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.64  thf('73', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64          = (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['75', '76'])).
% 0.46/0.64  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['77', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64          = (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['74', '79'])).
% 0.46/0.64  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('84', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64         = (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.46/0.64  thf('86', plain,
% 0.46/0.64      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64          = (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['60', '61', '72', '73', '85'])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64         = (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('simplify', [status(thm)], ['86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['47', '87'])).
% 0.46/0.64  thf(fc6_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.64         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.64         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf(t31_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.64         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.64           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.64           ( m1_subset_1 @
% 0.46/0.64             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X21)
% 0.46/0.64          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.46/0.64          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.46/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.46/0.64          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.46/0.64          | ~ (v1_funct_1 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.46/0.64        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.46/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64            != (k2_relat_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['90', '91'])).
% 0.46/0.64  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64         = (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.46/0.64  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.46/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['97'])).
% 0.46/0.64  thf('99', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.46/0.64          | ~ (v2_funct_1 @ X28)
% 0.46/0.64          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.46/0.64          | ~ (v1_funct_1 @ X28))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.64             (k2_struct_0 @ sk_A))
% 0.46/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['98', '99'])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X21)
% 0.46/0.64          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.46/0.64          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.46/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.46/0.64          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.46/0.64          | ~ (v1_funct_1 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.46/0.64        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64            != (k2_relat_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.64  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('105', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64         = (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.46/0.64  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.46/0.64  thf('109', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('simplify', [status(thm)], ['108'])).
% 0.46/0.64  thf('110', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf('111', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X21)
% 0.46/0.64          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.46/0.64          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.46/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.46/0.64          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.46/0.64          | ~ (v1_funct_1 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.64  thf('112', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.46/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.64           (k2_struct_0 @ sk_A))
% 0.46/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64            != (k2_relat_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['110', '111'])).
% 0.46/0.64  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('114', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.64  thf('115', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.64         = (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.46/0.64  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('117', plain,
% 0.46/0.64      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.64         (k2_struct_0 @ sk_A))
% 0.46/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.46/0.64  thf('118', plain,
% 0.46/0.64      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.64        (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('simplify', [status(thm)], ['117'])).
% 0.46/0.64  thf('119', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['97'])).
% 0.46/0.64  thf('120', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.46/0.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.64  thf('121', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['119', '120'])).
% 0.46/0.64  thf(t55_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v2_funct_1 @ A ) =>
% 0.46/0.64         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.64           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('122', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X1)
% 0.46/0.64          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf('123', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('124', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('125', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X1)
% 0.46/0.64          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf('126', plain,
% 0.46/0.64      (![X2 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X2)
% 0.46/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | ~ (v1_relat_1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.64  thf('127', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('128', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('129', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf('130', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('131', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X1)
% 0.46/0.64          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf('132', plain,
% 0.46/0.64      (![X2 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X2)
% 0.46/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | ~ (v1_relat_1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.64  thf('133', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X1)
% 0.46/0.64          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf('134', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         (((k1_relat_1 @ X13) != (X12))
% 0.46/0.64          | (v1_partfun1 @ X13 @ X12)
% 0.46/0.64          | ~ (v4_relat_1 @ X13 @ X12)
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.64  thf('135', plain,
% 0.46/0.64      (![X13 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X13)
% 0.46/0.64          | ~ (v4_relat_1 @ X13 @ (k1_relat_1 @ X13))
% 0.46/0.64          | (v1_partfun1 @ X13 @ (k1_relat_1 @ X13)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['134'])).
% 0.46/0.64  thf('136', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['133', '135'])).
% 0.46/0.64  thf('137', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['132', '136'])).
% 0.46/0.64  thf('138', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['131', '137'])).
% 0.46/0.64  thf('139', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['138'])).
% 0.46/0.64  thf('140', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['130', '139'])).
% 0.46/0.64  thf('141', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['140'])).
% 0.46/0.64  thf('142', plain,
% 0.46/0.64      ((~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['129', '141'])).
% 0.46/0.64  thf('143', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.64  thf('144', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X6 @ X7)
% 0.46/0.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('145', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['143', '144'])).
% 0.46/0.64  thf('146', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('148', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('149', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.64      inference('demod', [status(thm)], ['142', '145', '146', '147', '148'])).
% 0.46/0.64  thf('150', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('simplify', [status(thm)], ['108'])).
% 0.46/0.64  thf('151', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.64      inference('demod', [status(thm)], ['149', '150'])).
% 0.46/0.64  thf('152', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['128', '151'])).
% 0.46/0.64  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('156', plain,
% 0.46/0.64      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 0.46/0.64  thf('157', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['127', '156'])).
% 0.46/0.64  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('160', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('161', plain,
% 0.46/0.64      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 0.46/0.64  thf('162', plain,
% 0.46/0.64      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['126', '161'])).
% 0.46/0.64  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('166', plain,
% 0.46/0.64      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 0.46/0.64  thf('167', plain,
% 0.46/0.64      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['125', '166'])).
% 0.46/0.64  thf('168', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('simplify', [status(thm)], ['108'])).
% 0.46/0.64  thf('169', plain,
% 0.46/0.64      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['167', '168'])).
% 0.46/0.64  thf('170', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['124', '169'])).
% 0.46/0.64  thf('171', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('174', plain,
% 0.46/0.64      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['170', '171', '172', '173'])).
% 0.46/0.64  thf('175', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['123', '174'])).
% 0.46/0.64  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('178', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('179', plain,
% 0.46/0.64      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 0.46/0.64  thf('180', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         (~ (v1_partfun1 @ X13 @ X12)
% 0.46/0.64          | ((k1_relat_1 @ X13) = (X12))
% 0.46/0.64          | ~ (v4_relat_1 @ X13 @ X12)
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.64  thf('181', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['179', '180'])).
% 0.46/0.64  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('183', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf('184', plain,
% 0.46/0.64      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['181', '182', '183'])).
% 0.46/0.64  thf('185', plain,
% 0.46/0.64      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['122', '184'])).
% 0.46/0.64  thf('186', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf('187', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['143', '144'])).
% 0.46/0.64  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('191', plain,
% 0.46/0.64      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['185', '186', '187', '188', '189', '190'])).
% 0.46/0.64  thf('192', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['121', '191'])).
% 0.46/0.64  thf('193', plain,
% 0.46/0.64      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['100', '109', '118', '192'])).
% 0.46/0.64  thf('194', plain,
% 0.46/0.64      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['193'])).
% 0.46/0.64  thf('195', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['89', '194'])).
% 0.46/0.64  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('198', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('199', plain,
% 0.46/0.64      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 0.46/0.64  thf('200', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['88', '199'])).
% 0.46/0.64  thf('201', plain,
% 0.46/0.64      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64           sk_C)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '200'])).
% 0.46/0.64  thf('202', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.64  thf(redefinition_r2_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.64         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.64  thf('203', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.46/0.64          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.46/0.64          | ~ (v1_funct_1 @ X14)
% 0.46/0.64          | ~ (v1_funct_1 @ X17)
% 0.46/0.64          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.46/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.46/0.64          | (r2_funct_2 @ X15 @ X16 @ X14 @ X17)
% 0.46/0.64          | ((X14) != (X17)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.46/0.64  thf('204', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((r2_funct_2 @ X15 @ X16 @ X17 @ X17)
% 0.46/0.64          | ~ (v1_funct_1 @ X17)
% 0.46/0.64          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.46/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['203'])).
% 0.46/0.64  thf('205', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64           sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['202', '204'])).
% 0.46/0.64  thf('206', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('207', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('208', plain,
% 0.46/0.64      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['205', '206', '207'])).
% 0.46/0.64  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('211', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('212', plain, ($false),
% 0.46/0.64      inference('demod', [status(thm)], ['201', '208', '209', '210', '211'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
