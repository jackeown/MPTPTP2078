%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KIjpc7GGHL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:19 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  354 (11876 expanded)
%              Number of leaves         :   45 (3430 expanded)
%              Depth                    :   39
%              Number of atoms          : 3292 (246061 expanded)
%              Number of equality atoms :  174 (6948 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('35',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','43'])).

thf('45',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('64',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','43'])).

thf('65',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','70'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('74',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','61'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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
    inference('sup+',[status(thm)],['30','31'])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','61'])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('111',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','61'])).

thf('113',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','85','98','99','113'])).

thf('115',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['12','62','63','71','72','73','115'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('117',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
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

thf('119',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('120',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('123',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('124',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('130',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('131',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('134',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('139',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('140',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['128','137','146'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('148',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('149',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('150',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('152',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','61'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','61'])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('161',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('162',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','61'])).

thf('164',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156','159','164','165'])).

thf('167',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['150','166'])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('173',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['136'])).

thf('175',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('176',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('177',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('178',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('181',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['175','183'])).

thf('185',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('186',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['173','174','188'])).

thf('190',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('191',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('192',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('194',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('195',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('196',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('200',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('202',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['197','202'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('204',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('205',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('207',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('208',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('210',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','61'])).

thf('212',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('214',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('217',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('218',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('219',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('220',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('221',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('222',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('223',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('224',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('225',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('226',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k10_relat_1 @ X10 @ X11 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X10 ) @ X11 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['224','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['223','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['222','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('234',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['221','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['220','237'])).

thf('239',plain,(
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
    inference('sup-',[status(thm)],['219','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
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
    inference('sup-',[status(thm)],['218','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['217','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['216','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) @ ( k9_relat_1 @ sk_C @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['215','246'])).

thf('248',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['212','247'])).

thf('249',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('250',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('251',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('255',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('257',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','54','61'])).

thf('259',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('261',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['248','249','250','251','252','253','254','259','260'])).

thf('262',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('263',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['205','261','262'])).

thf('264',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['192','263'])).

thf('265',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['189','264'])).

thf('266',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['265'])).

thf('267',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['149','266'])).

thf('268',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('269',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['267','268','269','270'])).

thf('272',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('273',plain,(
    v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['271','272'])).

thf('274',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('275',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['267','268','269','270'])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('278',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('280',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['275','280'])).

thf('282',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['148','281'])).

thf('283',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('284',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('285',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['282','283','284','285','286'])).

thf('288',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('289',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('290',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['205','261','262'])).

thf('292',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['290','291'])).

thf('293',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['147','287','292'])).

thf('294',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['117','294'])).

thf('296',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('297',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['295','296','297','298'])).

thf('300',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

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

thf('301',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_funct_2 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('302',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['300','302'])).

thf('304',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('305',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['303','304','305'])).

thf('307',plain,(
    $false ),
    inference(demod,[status(thm)],['116','299','306'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KIjpc7GGHL
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 639 iterations in 0.270s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.55/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.73  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.55/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.55/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.73  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.55/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.55/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.55/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.55/0.73  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.55/0.73  thf(d3_struct_0, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.55/0.73  thf('0', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('2', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf(t64_tops_2, conjecture,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_struct_0 @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.73                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.73                 ( m1_subset_1 @
% 0.55/0.73                   C @ 
% 0.55/0.73                   ( k1_zfmisc_1 @
% 0.55/0.73                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.73               ( ( ( ( k2_relset_1 @
% 0.55/0.73                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.73                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.73                   ( v2_funct_1 @ C ) ) =>
% 0.55/0.73                 ( r2_funct_2 @
% 0.55/0.73                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.55/0.73                   ( k2_tops_2 @
% 0.55/0.73                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.73                     ( k2_tops_2 @
% 0.55/0.73                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.55/0.73                   C ) ) ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i]:
% 0.55/0.73        ( ( l1_struct_0 @ A ) =>
% 0.55/0.73          ( ![B:$i]:
% 0.55/0.73            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.55/0.73              ( ![C:$i]:
% 0.55/0.73                ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.73                    ( v1_funct_2 @
% 0.55/0.73                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.73                    ( m1_subset_1 @
% 0.55/0.73                      C @ 
% 0.55/0.73                      ( k1_zfmisc_1 @
% 0.55/0.73                        ( k2_zfmisc_1 @
% 0.55/0.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.73                  ( ( ( ( k2_relset_1 @
% 0.55/0.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.73                        ( k2_struct_0 @ B ) ) & 
% 0.55/0.73                      ( v2_funct_1 @ C ) ) =>
% 0.55/0.73                    ( r2_funct_2 @
% 0.55/0.73                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.55/0.73                      ( k2_tops_2 @
% 0.55/0.73                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.73                        ( k2_tops_2 @
% 0.55/0.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.55/0.73                      C ) ) ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.55/0.73  thf('3', plain,
% 0.55/0.73      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.73          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.73          sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.73            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.73           sk_C)
% 0.55/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.73  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('6', plain,
% 0.55/0.73      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.73          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.73          sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.55/0.73  thf('7', plain,
% 0.55/0.73      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.73           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.73            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.73           sk_C)
% 0.55/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup-', [status(thm)], ['1', '6'])).
% 0.55/0.73  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('9', plain,
% 0.55/0.73      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.73          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.73          sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.55/0.73  thf('10', plain,
% 0.55/0.73      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.73           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.73            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.73           sk_C)
% 0.55/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup-', [status(thm)], ['0', '9'])).
% 0.55/0.73  thf('11', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('12', plain,
% 0.55/0.73      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.73          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.73           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.73          sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['10', '11'])).
% 0.55/0.73  thf('13', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('14', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('15', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('16', plain,
% 0.55/0.73      (((m1_subset_1 @ sk_C @ 
% 0.55/0.73         (k1_zfmisc_1 @ 
% 0.55/0.73          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.55/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['14', '15'])).
% 0.55/0.73  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('18', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.55/0.73      inference('demod', [status(thm)], ['16', '17'])).
% 0.55/0.73  thf(cc5_funct_2, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.55/0.73       ( ![C:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.73           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.55/0.73             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.55/0.73  thf('19', plain,
% 0.55/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.55/0.73          | (v1_partfun1 @ X19 @ X20)
% 0.55/0.73          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.55/0.73          | ~ (v1_funct_1 @ X19)
% 0.55/0.73          | (v1_xboole_0 @ X21))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.55/0.73  thf('20', plain,
% 0.55/0.73      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.55/0.73        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.73        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.55/0.73        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('22', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('23', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('24', plain,
% 0.55/0.73      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.55/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['22', '23'])).
% 0.55/0.73  thf('25', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('26', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['24', '25'])).
% 0.55/0.73  thf('27', plain,
% 0.55/0.73      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.55/0.73        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('demod', [status(thm)], ['20', '21', '26'])).
% 0.55/0.73  thf('28', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.55/0.73  thf('29', plain,
% 0.55/0.73      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.73         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.55/0.73          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.55/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.73  thf('30', plain,
% 0.55/0.73      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.73         = (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.55/0.73  thf('31', plain,
% 0.55/0.73      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.73         = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('33', plain,
% 0.55/0.73      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.55/0.73        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('demod', [status(thm)], ['27', '32'])).
% 0.55/0.73  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('35', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf(fc2_struct_0, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.55/0.73       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.55/0.73  thf('36', plain,
% 0.55/0.73      (![X32 : $i]:
% 0.55/0.73         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.55/0.73          | ~ (l1_struct_0 @ X32)
% 0.55/0.73          | (v2_struct_0 @ X32))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.55/0.73  thf('37', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.55/0.73          | ~ (l1_struct_0 @ X0)
% 0.55/0.73          | (v2_struct_0 @ X0)
% 0.55/0.73          | ~ (l1_struct_0 @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.73  thf('38', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((v2_struct_0 @ X0)
% 0.55/0.73          | ~ (l1_struct_0 @ X0)
% 0.55/0.73          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.55/0.73      inference('simplify', [status(thm)], ['37'])).
% 0.55/0.73  thf('39', plain,
% 0.55/0.73      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.55/0.73        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.73        | (v2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup-', [status(thm)], ['34', '38'])).
% 0.55/0.73  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('41', plain,
% 0.55/0.73      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['39', '40'])).
% 0.55/0.73  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('43', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('clc', [status(thm)], ['41', '42'])).
% 0.55/0.73  thf('44', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('clc', [status(thm)], ['33', '43'])).
% 0.55/0.73  thf('45', plain,
% 0.55/0.73      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup+', [status(thm)], ['13', '44'])).
% 0.55/0.73  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('47', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['45', '46'])).
% 0.55/0.73  thf(d4_partfun1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.55/0.73       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.55/0.73  thf('48', plain,
% 0.55/0.73      (![X22 : $i, X23 : $i]:
% 0.55/0.73         (~ (v1_partfun1 @ X23 @ X22)
% 0.55/0.73          | ((k1_relat_1 @ X23) = (X22))
% 0.55/0.73          | ~ (v4_relat_1 @ X23 @ X22)
% 0.55/0.73          | ~ (v1_relat_1 @ X23))),
% 0.55/0.73      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.55/0.73  thf('49', plain,
% 0.55/0.73      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.73        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.55/0.73        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.55/0.73  thf('50', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(cc2_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.55/0.73  thf('51', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.73          | (v1_relat_1 @ X0)
% 0.55/0.73          | ~ (v1_relat_1 @ X1))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.73  thf('52', plain,
% 0.55/0.73      ((~ (v1_relat_1 @ 
% 0.55/0.73           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.55/0.73        | (v1_relat_1 @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['50', '51'])).
% 0.55/0.73  thf(fc6_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.55/0.73  thf('53', plain,
% 0.55/0.73      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.73  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.73  thf('55', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('56', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('57', plain,
% 0.55/0.73      (((m1_subset_1 @ sk_C @ 
% 0.55/0.73         (k1_zfmisc_1 @ 
% 0.55/0.73          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup+', [status(thm)], ['55', '56'])).
% 0.55/0.73  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('59', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('demod', [status(thm)], ['57', '58'])).
% 0.55/0.73  thf(cc2_relset_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.73  thf('60', plain,
% 0.55/0.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.73         ((v4_relat_1 @ X13 @ X14)
% 0.55/0.73          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.73  thf('61', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['59', '60'])).
% 0.55/0.73  thf('62', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['49', '54', '61'])).
% 0.55/0.73  thf('63', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('64', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('clc', [status(thm)], ['33', '43'])).
% 0.55/0.73  thf('65', plain,
% 0.55/0.73      (![X22 : $i, X23 : $i]:
% 0.55/0.73         (~ (v1_partfun1 @ X23 @ X22)
% 0.55/0.73          | ((k1_relat_1 @ X23) = (X22))
% 0.55/0.73          | ~ (v4_relat_1 @ X23 @ X22)
% 0.55/0.73          | ~ (v1_relat_1 @ X23))),
% 0.55/0.73      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.55/0.73  thf('66', plain,
% 0.55/0.73      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.73        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.55/0.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['64', '65'])).
% 0.55/0.73  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.73      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.73  thf('68', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('69', plain,
% 0.55/0.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.73         ((v4_relat_1 @ X13 @ X14)
% 0.55/0.73          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.73  thf('70', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['68', '69'])).
% 0.55/0.73  thf('71', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['66', '67', '70'])).
% 0.55/0.73  thf('72', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['66', '67', '70'])).
% 0.55/0.73  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('74', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('75', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.73      inference('demod', [status(thm)], ['57', '58'])).
% 0.55/0.73  thf('76', plain,
% 0.55/0.73      (((m1_subset_1 @ sk_C @ 
% 0.55/0.73         (k1_zfmisc_1 @ 
% 0.55/0.73          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.55/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['74', '75'])).
% 0.55/0.73  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('78', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.55/0.73      inference('demod', [status(thm)], ['76', '77'])).
% 0.55/0.73  thf('79', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('80', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.73      inference('demod', [status(thm)], ['78', '79'])).
% 0.55/0.73  thf('81', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['49', '54', '61'])).
% 0.55/0.73  thf('82', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.73      inference('demod', [status(thm)], ['80', '81'])).
% 0.55/0.73  thf(d4_tops_2, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.73       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.55/0.73         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.55/0.73  thf('83', plain,
% 0.55/0.73      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.55/0.73         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.55/0.73          | ~ (v2_funct_1 @ X35)
% 0.55/0.73          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.55/0.73          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.55/0.73          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.55/0.73          | ~ (v1_funct_1 @ X35))),
% 0.55/0.73      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.55/0.73  thf('84', plain,
% 0.55/0.73      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.73        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.55/0.73        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73            = (k2_funct_1 @ sk_C))
% 0.55/0.73        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.73        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73            != (k2_relat_1 @ sk_C)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['82', '83'])).
% 0.55/0.73  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('86', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('87', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('88', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('89', plain,
% 0.55/0.73      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup+', [status(thm)], ['87', '88'])).
% 0.55/0.73  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('91', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['89', '90'])).
% 0.55/0.73  thf('92', plain,
% 0.55/0.73      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.55/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['86', '91'])).
% 0.55/0.73  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('94', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['92', '93'])).
% 0.55/0.73  thf('95', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('96', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['94', '95'])).
% 0.55/0.73  thf('97', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['49', '54', '61'])).
% 0.55/0.73  thf('98', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['96', '97'])).
% 0.55/0.73  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('100', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('101', plain,
% 0.55/0.73      (![X31 : $i]:
% 0.55/0.73         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.73  thf('102', plain,
% 0.55/0.73      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.73         = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('103', plain,
% 0.55/0.73      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.73          = (k2_struct_0 @ sk_B))
% 0.55/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.73      inference('sup+', [status(thm)], ['101', '102'])).
% 0.55/0.73  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('105', plain,
% 0.55/0.73      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.73         = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['103', '104'])).
% 0.55/0.73  thf('106', plain,
% 0.55/0.73      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.55/0.73          = (k2_struct_0 @ sk_B))
% 0.55/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['100', '105'])).
% 0.55/0.73  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('108', plain,
% 0.55/0.73      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.55/0.73         = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['106', '107'])).
% 0.55/0.73  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('110', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('111', plain,
% 0.55/0.73      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73         = (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.55/0.73  thf('112', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['49', '54', '61'])).
% 0.55/0.73  thf('113', plain,
% 0.55/0.73      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73         = (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['111', '112'])).
% 0.55/0.73  thf('114', plain,
% 0.55/0.73      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73          = (k2_funct_1 @ sk_C))
% 0.55/0.73        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.55/0.73      inference('demod', [status(thm)], ['84', '85', '98', '99', '113'])).
% 0.55/0.73  thf('115', plain,
% 0.55/0.73      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73         = (k2_funct_1 @ sk_C))),
% 0.55/0.73      inference('simplify', [status(thm)], ['114'])).
% 0.55/0.73  thf('116', plain,
% 0.55/0.73      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.73          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.73           (k2_funct_1 @ sk_C)) @ 
% 0.55/0.73          sk_C)),
% 0.55/0.73      inference('demod', [status(thm)],
% 0.55/0.73                ['12', '62', '63', '71', '72', '73', '115'])).
% 0.55/0.73  thf(fc6_funct_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.55/0.73       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.55/0.73         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.55/0.73         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.55/0.73  thf('117', plain,
% 0.55/0.73      (![X9 : $i]:
% 0.55/0.73         ((v2_funct_1 @ (k2_funct_1 @ X9))
% 0.55/0.73          | ~ (v2_funct_1 @ X9)
% 0.55/0.73          | ~ (v1_funct_1 @ X9)
% 0.55/0.73          | ~ (v1_relat_1 @ X9))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.73  thf('118', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.73      inference('demod', [status(thm)], ['80', '81'])).
% 0.55/0.73  thf(t31_funct_2, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.73       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.55/0.73         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.55/0.73           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.55/0.73           ( m1_subset_1 @
% 0.55/0.73             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.55/0.73  thf('119', plain,
% 0.55/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.73         (~ (v2_funct_1 @ X28)
% 0.55/0.73          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.55/0.73          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 0.55/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.55/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.55/0.73          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.55/0.73          | ~ (v1_funct_1 @ X28))),
% 0.55/0.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.73  thf('120', plain,
% 0.55/0.73      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.73        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.55/0.73        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.73           (k1_zfmisc_1 @ 
% 0.55/0.73            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.55/0.73        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73            != (k2_relat_1 @ sk_C))
% 0.55/0.73        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['118', '119'])).
% 0.55/0.73  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('122', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['96', '97'])).
% 0.55/0.73  thf('123', plain,
% 0.55/0.73      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73         = (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['111', '112'])).
% 0.55/0.73  thf('124', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('125', plain,
% 0.55/0.73      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.73         (k1_zfmisc_1 @ 
% 0.55/0.73          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.55/0.73        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.55/0.73      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 0.55/0.73  thf('126', plain,
% 0.55/0.73      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['125'])).
% 0.55/0.73  thf('127', plain,
% 0.55/0.73      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.55/0.73         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.55/0.73          | ~ (v2_funct_1 @ X35)
% 0.55/0.73          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.55/0.73          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.55/0.73          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.55/0.73          | ~ (v1_funct_1 @ X35))),
% 0.55/0.73      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.55/0.73  thf('128', plain,
% 0.55/0.73      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.73        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.55/0.73             (k1_relat_1 @ sk_C))
% 0.55/0.73        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.73            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.73        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.73        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.73            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['126', '127'])).
% 0.55/0.73  thf('129', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.73      inference('demod', [status(thm)], ['80', '81'])).
% 0.55/0.73  thf('130', plain,
% 0.55/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.73         (~ (v2_funct_1 @ X28)
% 0.55/0.73          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.55/0.73          | (v1_funct_1 @ (k2_funct_1 @ X28))
% 0.55/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.55/0.73          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.55/0.73          | ~ (v1_funct_1 @ X28))),
% 0.55/0.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.73  thf('131', plain,
% 0.55/0.73      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.73        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.55/0.73        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.73        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73            != (k2_relat_1 @ sk_C))
% 0.55/0.73        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['129', '130'])).
% 0.55/0.73  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('133', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['96', '97'])).
% 0.55/0.73  thf('134', plain,
% 0.55/0.73      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73         = (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['111', '112'])).
% 0.55/0.73  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('136', plain,
% 0.55/0.73      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.73        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.55/0.73      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 0.55/0.73  thf('137', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.73      inference('simplify', [status(thm)], ['136'])).
% 0.55/0.73  thf('138', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ 
% 0.55/0.73        (k1_zfmisc_1 @ 
% 0.55/0.73         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.73      inference('demod', [status(thm)], ['80', '81'])).
% 0.55/0.73  thf('139', plain,
% 0.55/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.73         (~ (v2_funct_1 @ X28)
% 0.55/0.73          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.55/0.73          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 0.55/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.55/0.73          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.55/0.73          | ~ (v1_funct_1 @ X28))),
% 0.55/0.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.73  thf('140', plain,
% 0.55/0.73      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.73        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.55/0.73        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.55/0.73           (k1_relat_1 @ sk_C))
% 0.55/0.73        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73            != (k2_relat_1 @ sk_C))
% 0.55/0.73        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['138', '139'])).
% 0.55/0.73  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('142', plain,
% 0.55/0.73      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['96', '97'])).
% 0.55/0.73  thf('143', plain,
% 0.55/0.73      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.73         = (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['111', '112'])).
% 0.55/0.73  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('145', plain,
% 0.55/0.73      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.55/0.73         (k1_relat_1 @ sk_C))
% 0.55/0.73        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.55/0.73      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 0.55/0.73  thf('146', plain,
% 0.55/0.73      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.55/0.73        (k1_relat_1 @ sk_C))),
% 0.55/0.73      inference('simplify', [status(thm)], ['145'])).
% 0.55/0.73  thf('147', plain,
% 0.55/0.73      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.73          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.73        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.73        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.73            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.55/0.73      inference('demod', [status(thm)], ['128', '137', '146'])).
% 0.55/0.73  thf(t65_funct_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.73       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.55/0.74  thf('148', plain,
% 0.55/0.74      (![X12 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X12)
% 0.55/0.74          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.55/0.74          | ~ (v1_funct_1 @ X12)
% 0.55/0.74          | ~ (v1_relat_1 @ X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.55/0.74  thf('149', plain,
% 0.55/0.74      (![X9 : $i]:
% 0.55/0.74         ((v2_funct_1 @ (k2_funct_1 @ X9))
% 0.55/0.74          | ~ (v2_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_relat_1 @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.74  thf('150', plain,
% 0.55/0.74      (![X31 : $i]:
% 0.55/0.74         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.74  thf('151', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.55/0.74  thf('152', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['49', '54', '61'])).
% 0.55/0.74  thf('153', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('demod', [status(thm)], ['151', '152'])).
% 0.55/0.74  thf('154', plain,
% 0.55/0.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X28)
% 0.55/0.74          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.55/0.74          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.55/0.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.55/0.74          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.55/0.74          | ~ (v1_funct_1 @ X28))),
% 0.55/0.74      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.74  thf('155', plain,
% 0.55/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74           (k1_zfmisc_1 @ 
% 0.55/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.55/0.74        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74            != (u1_struct_0 @ sk_B))
% 0.55/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['153', '154'])).
% 0.55/0.74  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('157', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['89', '90'])).
% 0.55/0.74  thf('158', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['49', '54', '61'])).
% 0.55/0.74  thf('159', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['157', '158'])).
% 0.55/0.74  thf('160', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.55/0.74  thf('161', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.74         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.55/0.74          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.74  thf('162', plain,
% 0.55/0.74      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74         = (k2_relat_1 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['160', '161'])).
% 0.55/0.74  thf('163', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['49', '54', '61'])).
% 0.55/0.74  thf('164', plain,
% 0.55/0.74      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74         = (k2_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['162', '163'])).
% 0.55/0.74  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('166', plain,
% 0.55/0.74      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74         (k1_zfmisc_1 @ 
% 0.55/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.55/0.74        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['155', '156', '159', '164', '165'])).
% 0.55/0.74  thf('167', plain,
% 0.55/0.74      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.55/0.74        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.74        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74           (k1_zfmisc_1 @ 
% 0.55/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['150', '166'])).
% 0.55/0.74  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.74  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('170', plain,
% 0.55/0.74      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.55/0.74        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74           (k1_zfmisc_1 @ 
% 0.55/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.55/0.74      inference('demod', [status(thm)], ['167', '168', '169'])).
% 0.55/0.74  thf('171', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['170'])).
% 0.55/0.74  thf('172', plain,
% 0.55/0.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X28)
% 0.55/0.74          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.55/0.74          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 0.55/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.55/0.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.55/0.74          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.55/0.74          | ~ (v1_funct_1 @ X28))),
% 0.55/0.74      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.74  thf('173', plain,
% 0.55/0.74      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74             (k1_relat_1 @ sk_C))
% 0.55/0.74        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74           (k1_zfmisc_1 @ 
% 0.55/0.74            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.55/0.74        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.55/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['171', '172'])).
% 0.55/0.74  thf('174', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.74      inference('simplify', [status(thm)], ['136'])).
% 0.55/0.74  thf('175', plain,
% 0.55/0.74      (![X31 : $i]:
% 0.55/0.74         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.55/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.74  thf('176', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('demod', [status(thm)], ['151', '152'])).
% 0.55/0.74  thf('177', plain,
% 0.55/0.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X28)
% 0.55/0.74          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.55/0.74          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 0.55/0.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.55/0.74          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.55/0.74          | ~ (v1_funct_1 @ X28))),
% 0.55/0.74      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.55/0.74  thf('178', plain,
% 0.55/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74           (k1_relat_1 @ sk_C))
% 0.55/0.74        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74            != (u1_struct_0 @ sk_B))
% 0.55/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['176', '177'])).
% 0.55/0.74  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('180', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['157', '158'])).
% 0.55/0.74  thf('181', plain,
% 0.55/0.74      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74         = (k2_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['162', '163'])).
% 0.55/0.74  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('183', plain,
% 0.55/0.74      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74         (k1_relat_1 @ sk_C))
% 0.55/0.74        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 0.55/0.74  thf('184', plain,
% 0.55/0.74      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.55/0.74        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.74        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74           (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['175', '183'])).
% 0.55/0.74  thf('185', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.74  thf('186', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('187', plain,
% 0.55/0.74      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.55/0.74        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74           (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['184', '185', '186'])).
% 0.55/0.74  thf('188', plain,
% 0.55/0.74      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74        (k1_relat_1 @ sk_C))),
% 0.55/0.74      inference('simplify', [status(thm)], ['187'])).
% 0.55/0.74  thf('189', plain,
% 0.55/0.74      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74         (k1_zfmisc_1 @ 
% 0.55/0.74          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.55/0.74        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.55/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['173', '174', '188'])).
% 0.55/0.74  thf('190', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['170'])).
% 0.55/0.74  thf('191', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.74         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.55/0.74          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.74  thf('192', plain,
% 0.55/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['190', '191'])).
% 0.55/0.74  thf('193', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['125'])).
% 0.55/0.74  thf('194', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.74         ((v4_relat_1 @ X13 @ X14)
% 0.55/0.74          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.74  thf('195', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['193', '194'])).
% 0.55/0.74  thf(t209_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.55/0.74       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.55/0.74  thf('196', plain,
% 0.55/0.74      (![X7 : $i, X8 : $i]:
% 0.55/0.74         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.55/0.74          | ~ (v4_relat_1 @ X7 @ X8)
% 0.55/0.74          | ~ (v1_relat_1 @ X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.55/0.74  thf('197', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74        | ((k2_funct_1 @ sk_C)
% 0.55/0.74            = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['195', '196'])).
% 0.55/0.74  thf('198', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['125'])).
% 0.55/0.74  thf('199', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.74          | (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.74  thf('200', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ 
% 0.55/0.74           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.55/0.74        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['198', '199'])).
% 0.55/0.74  thf('201', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.74  thf('202', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['200', '201'])).
% 0.55/0.74  thf('203', plain,
% 0.55/0.74      (((k2_funct_1 @ sk_C)
% 0.55/0.74         = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['197', '202'])).
% 0.55/0.74  thf(t148_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ B ) =>
% 0.55/0.74       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.55/0.74  thf('204', plain,
% 0.55/0.74      (![X4 : $i, X5 : $i]:
% 0.55/0.74         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.55/0.74          | ~ (v1_relat_1 @ X4))),
% 0.55/0.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.55/0.74  thf('205', plain,
% 0.55/0.74      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 0.55/0.74        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['203', '204'])).
% 0.55/0.74  thf('206', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['59', '60'])).
% 0.55/0.74  thf('207', plain,
% 0.55/0.74      (![X7 : $i, X8 : $i]:
% 0.55/0.74         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.55/0.74          | ~ (v4_relat_1 @ X7 @ X8)
% 0.55/0.74          | ~ (v1_relat_1 @ X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.55/0.74  thf('208', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.74        | ((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['206', '207'])).
% 0.55/0.74  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.74  thf('210', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['208', '209'])).
% 0.55/0.74  thf('211', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['49', '54', '61'])).
% 0.55/0.74  thf('212', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['210', '211'])).
% 0.55/0.74  thf('213', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.74  thf('214', plain,
% 0.55/0.74      (![X4 : $i, X5 : $i]:
% 0.55/0.74         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.55/0.74          | ~ (v1_relat_1 @ X4))),
% 0.55/0.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.55/0.74  thf('215', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['213', '214'])).
% 0.55/0.74  thf('216', plain,
% 0.55/0.74      (![X12 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X12)
% 0.55/0.74          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.55/0.74          | ~ (v1_funct_1 @ X12)
% 0.55/0.74          | ~ (v1_relat_1 @ X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.55/0.74  thf('217', plain,
% 0.55/0.74      (![X9 : $i]:
% 0.55/0.74         ((v2_funct_1 @ (k2_funct_1 @ X9))
% 0.55/0.74          | ~ (v2_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_relat_1 @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.74  thf('218', plain,
% 0.55/0.74      (![X9 : $i]:
% 0.55/0.74         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.55/0.74          | ~ (v2_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_relat_1 @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.74  thf('219', plain,
% 0.55/0.74      (![X9 : $i]:
% 0.55/0.74         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.55/0.74          | ~ (v2_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_relat_1 @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.74  thf('220', plain,
% 0.55/0.74      (![X12 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X12)
% 0.55/0.74          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.55/0.74          | ~ (v1_funct_1 @ X12)
% 0.55/0.74          | ~ (v1_relat_1 @ X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.55/0.74  thf('221', plain,
% 0.55/0.74      (![X9 : $i]:
% 0.55/0.74         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.55/0.74          | ~ (v2_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_relat_1 @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.74  thf('222', plain,
% 0.55/0.74      (![X9 : $i]:
% 0.55/0.74         ((v2_funct_1 @ (k2_funct_1 @ X9))
% 0.55/0.74          | ~ (v2_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_relat_1 @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.74  thf('223', plain,
% 0.55/0.74      (![X9 : $i]:
% 0.55/0.74         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.55/0.74          | ~ (v2_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_relat_1 @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.74  thf('224', plain,
% 0.55/0.74      (![X9 : $i]:
% 0.55/0.74         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.55/0.74          | ~ (v2_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_funct_1 @ X9)
% 0.55/0.74          | ~ (v1_relat_1 @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.74  thf('225', plain,
% 0.55/0.74      (![X12 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X12)
% 0.55/0.74          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.55/0.74          | ~ (v1_funct_1 @ X12)
% 0.55/0.74          | ~ (v1_relat_1 @ X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.55/0.74  thf(t155_funct_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.74       ( ( v2_funct_1 @ B ) =>
% 0.55/0.74         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.55/0.74  thf('226', plain,
% 0.55/0.74      (![X10 : $i, X11 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X10)
% 0.55/0.74          | ((k10_relat_1 @ X10 @ X11)
% 0.55/0.74              = (k9_relat_1 @ (k2_funct_1 @ X10) @ X11))
% 0.55/0.74          | ~ (v1_funct_1 @ X10)
% 0.55/0.74          | ~ (v1_relat_1 @ X10))),
% 0.55/0.74      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.55/0.74  thf('227', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['225', '226'])).
% 0.55/0.74  thf('228', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['224', '227'])).
% 0.55/0.74  thf('229', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 0.55/0.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['228'])).
% 0.55/0.74  thf('230', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['223', '229'])).
% 0.55/0.74  thf('231', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['230'])).
% 0.55/0.74  thf('232', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['222', '231'])).
% 0.55/0.74  thf('233', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['232'])).
% 0.55/0.74  thf(t169_relat_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ A ) =>
% 0.55/0.74       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.55/0.74  thf('234', plain,
% 0.55/0.74      (![X6 : $i]:
% 0.55/0.74         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.55/0.74          | ~ (v1_relat_1 @ X6))),
% 0.55/0.74      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.55/0.74  thf('235', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.55/0.74            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['233', '234'])).
% 0.55/0.74  thf('236', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.55/0.74              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['221', '235'])).
% 0.55/0.74  thf('237', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.55/0.74            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['236'])).
% 0.55/0.74  thf('238', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.55/0.74            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['220', '237'])).
% 0.55/0.74  thf('239', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.55/0.74              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['219', '238'])).
% 0.55/0.74  thf('240', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.55/0.74            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.55/0.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['239'])).
% 0.55/0.74  thf('241', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.55/0.74              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['218', '240'])).
% 0.55/0.74  thf('242', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.55/0.74            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.55/0.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['241'])).
% 0.55/0.74  thf('243', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.55/0.74              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['217', '242'])).
% 0.55/0.74  thf('244', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.55/0.74            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['243'])).
% 0.55/0.74  thf('245', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.55/0.74            = (k1_relat_1 @ X0))
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v2_funct_1 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['216', '244'])).
% 0.55/0.74  thf('246', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.55/0.74              = (k1_relat_1 @ X0)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['245'])).
% 0.55/0.74  thf('247', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k9_relat_1 @ (k2_funct_1 @ (k7_relat_1 @ sk_C @ X0)) @ 
% 0.55/0.74            (k9_relat_1 @ sk_C @ X0)) = (k1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.55/0.74          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ X0))
% 0.55/0.74          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ (k7_relat_1 @ sk_C @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['215', '246'])).
% 0.55/0.74  thf('248', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.74        | ~ (v2_funct_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.55/0.74        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.55/0.74        | ((k9_relat_1 @ 
% 0.55/0.74            (k2_funct_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))) @ 
% 0.55/0.74            (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.55/0.74            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['212', '247'])).
% 0.55/0.74  thf('249', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.74  thf('250', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['210', '211'])).
% 0.55/0.74  thf('251', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('252', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['210', '211'])).
% 0.55/0.74  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('254', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['210', '211'])).
% 0.55/0.74  thf('255', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['208', '209'])).
% 0.55/0.74  thf('256', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['213', '214'])).
% 0.55/0.74  thf('257', plain,
% 0.55/0.74      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['255', '256'])).
% 0.55/0.74  thf('258', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['49', '54', '61'])).
% 0.55/0.74  thf('259', plain,
% 0.55/0.74      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['257', '258'])).
% 0.55/0.74  thf('260', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['210', '211'])).
% 0.55/0.74  thf('261', plain,
% 0.55/0.74      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.55/0.74         = (k1_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)],
% 0.55/0.74                ['248', '249', '250', '251', '252', '253', '254', '259', '260'])).
% 0.55/0.74  thf('262', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['200', '201'])).
% 0.55/0.74  thf('263', plain,
% 0.55/0.74      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['205', '261', '262'])).
% 0.55/0.74  thf('264', plain,
% 0.55/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['192', '263'])).
% 0.55/0.74  thf('265', plain,
% 0.55/0.74      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74         (k1_zfmisc_1 @ 
% 0.55/0.74          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.55/0.74        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.55/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['189', '264'])).
% 0.55/0.74  thf('266', plain,
% 0.55/0.74      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74           (k1_zfmisc_1 @ 
% 0.55/0.74            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['265'])).
% 0.55/0.74  thf('267', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.74        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74           (k1_zfmisc_1 @ 
% 0.55/0.74            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['149', '266'])).
% 0.55/0.74  thf('268', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.74  thf('269', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('270', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('271', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('demod', [status(thm)], ['267', '268', '269', '270'])).
% 0.55/0.74  thf('272', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.74         ((v4_relat_1 @ X13 @ X14)
% 0.55/0.74          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.74  thf('273', plain,
% 0.55/0.74      ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['271', '272'])).
% 0.55/0.74  thf('274', plain,
% 0.55/0.74      (![X7 : $i, X8 : $i]:
% 0.55/0.74         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.55/0.74          | ~ (v4_relat_1 @ X7 @ X8)
% 0.55/0.74          | ~ (v1_relat_1 @ X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.55/0.74  thf('275', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.74        | ((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74            = (k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74               (k1_relat_1 @ sk_C))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['273', '274'])).
% 0.55/0.74  thf('276', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('demod', [status(thm)], ['267', '268', '269', '270'])).
% 0.55/0.74  thf('277', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.74          | (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.74  thf('278', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ 
% 0.55/0.74           (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))
% 0.55/0.74        | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['276', '277'])).
% 0.55/0.74  thf('279', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.74  thf('280', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['278', '279'])).
% 0.55/0.74  thf('281', plain,
% 0.55/0.74      (((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74         = (k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74            (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['275', '280'])).
% 0.55/0.74  thf('282', plain,
% 0.55/0.74      ((((k2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74          = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.55/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.74      inference('sup+', [status(thm)], ['148', '281'])).
% 0.55/0.74  thf('283', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['210', '211'])).
% 0.55/0.74  thf('284', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.74  thf('285', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('286', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('287', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['282', '283', '284', '285', '286'])).
% 0.55/0.74  thf('288', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['125'])).
% 0.55/0.74  thf('289', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.74         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.55/0.74          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.74  thf('290', plain,
% 0.55/0.74      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['288', '289'])).
% 0.55/0.74  thf('291', plain,
% 0.55/0.74      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['205', '261', '262'])).
% 0.55/0.74  thf('292', plain,
% 0.55/0.74      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['290', '291'])).
% 0.55/0.74  thf('293', plain,
% 0.55/0.74      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.55/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['147', '287', '292'])).
% 0.55/0.74  thf('294', plain,
% 0.55/0.74      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['293'])).
% 0.55/0.74  thf('295', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.74        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['117', '294'])).
% 0.55/0.74  thf('296', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.74  thf('297', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('298', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('299', plain,
% 0.55/0.74      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.55/0.74         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['295', '296', '297', '298'])).
% 0.55/0.74  thf('300', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('demod', [status(thm)], ['151', '152'])).
% 0.55/0.74  thf(redefinition_r2_funct_2, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.74         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.74       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.55/0.74  thf('301', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.55/0.74          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.55/0.74          | ~ (v1_funct_1 @ X24)
% 0.55/0.74          | ~ (v1_funct_1 @ X27)
% 0.55/0.74          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.55/0.74          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.55/0.74          | (r2_funct_2 @ X25 @ X26 @ X24 @ X27)
% 0.55/0.74          | ((X24) != (X27)))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.55/0.74  thf('302', plain,
% 0.55/0.74      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.74         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 0.55/0.74          | ~ (v1_funct_1 @ X27)
% 0.55/0.74          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.55/0.74          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['301'])).
% 0.55/0.74  thf('303', plain,
% 0.55/0.74      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.55/0.74           sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['300', '302'])).
% 0.55/0.74  thf('304', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['157', '158'])).
% 0.55/0.74  thf('305', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('306', plain,
% 0.55/0.74      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['303', '304', '305'])).
% 0.55/0.74  thf('307', plain, ($false),
% 0.55/0.74      inference('demod', [status(thm)], ['116', '299', '306'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
