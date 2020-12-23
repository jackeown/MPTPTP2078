%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Xrd3tbyaN

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:51 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  370 (23126 expanded)
%              Number of leaves         :   51 (6724 expanded)
%              Depth                    :   42
%              Number of atoms          : 3268 (516114 expanded)
%              Number of equality atoms :  220 (27591 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

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

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
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

thf('7',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X36 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('58',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('62',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['37','62'])).

thf('64',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('68',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('77',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
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

thf('79',plain,(
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

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('85',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('87',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','76','92','93'])).

thf('95',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('96',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','96'])).

thf('98',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X36 @ X37 @ X38 ) @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('106',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('107',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['98','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('110',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['110','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
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

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['126','131'])).

thf('133',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','137'])).

thf('139',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109','139','140'])).

thf('142',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('143',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['97','143'])).

thf('145',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['145'])).

thf('147',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('148',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('149',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['91'])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('151',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

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

thf('154',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_partfun1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X28 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('155',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X30 @ X28 )
      | ( v1_partfun1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','155'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('159',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('160',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('161',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('164',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('165',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['161','162','165'])).

thf('167',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['152','166'])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('171',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('172',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','76','92','93'])).

thf('173',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('174',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('176',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('181',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
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

thf('183',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('186',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('191',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('194',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('199',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('200',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','184','191','192','200'])).

thf('202',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('204',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('205',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('206',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['145'])).

thf('207',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','209'])).

thf('211',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['203','212'])).

thf('214',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['202','213'])).

thf('215',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','214'])).

thf('216',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('218',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['216','217','218','219'])).

thf('221',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','220'])).

thf('222',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X7: $i] :
      ( ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('224',plain,
    ( ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('226',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('227',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('229',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('231',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['145'])).

thf('233',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['231','232'])).

thf('234',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['151','233'])).

thf('235',plain,
    ( ( ( u1_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','234'])).

thf('236',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','76','92','93'])).

thf('237',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X30 @ X28 )
      | ( v1_partfun1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('238',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('240',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X36 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('241',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('244',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['201'])).

thf('246',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109','139','140'])).

thf('248',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['238','246','247'])).

thf('249',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('250',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','76','92','93'])).

thf('252',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('253',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','76','92','93'])).

thf('255',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('256',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['250','253','256'])).

thf('258',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('259',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('260',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('261',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['259','260'])).

thf('262',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('263',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['261','262','263'])).

thf('265',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('266',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != X26 )
      | ( v1_partfun1 @ X27 @ X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('267',plain,(
    ! [X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v4_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) )
      | ( v1_partfun1 @ X27 @ ( k1_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['265','267'])).

thf('269',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['264','268'])).

thf('270',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('271',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('274',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['269','270','271','272','273'])).

thf('275',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['258','274'])).

thf('276',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('277',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['275','276','277','278'])).

thf('280',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('281',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['279','280'])).

thf('282',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('283',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['261','262','263'])).

thf('284',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['281','282','283'])).

thf('285',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['257','284'])).

thf('286',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['235','285'])).

thf('287',plain,(
    v1_funct_2 @ sk_C @ k1_xboole_0 @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','286'])).

thf('288',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('289',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['235','285'])).

thf('290',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('291',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['290'])).

thf('292',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['288','289','291'])).

thf('293',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X30 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_partfun1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X28 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('294',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ k1_xboole_0 @ X28 )
      | ( v1_partfun1 @ X29 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['290'])).

thf('296',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ k1_xboole_0 @ X28 )
      | ( v1_partfun1 @ X29 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('297',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['292','296'])).

thf('298',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,(
    v1_partfun1 @ sk_C @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['287','299'])).

thf('301',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('302',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('304',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['288','289','291'])).

thf('305',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('306',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('307',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['304','307'])).

thf('309',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['302','303','308'])).

thf('310',plain,(
    ! [X7: $i] :
      ( ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('311',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['309','310'])).

thf('312',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['290'])).

thf('313',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('314',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['311','312','313'])).

thf('315',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('316',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    $false ),
    inference(demod,[status(thm)],['15','316'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Xrd3tbyaN
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 2.21/2.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.21/2.46  % Solved by: fo/fo7.sh
% 2.21/2.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.21/2.46  % done 1679 iterations in 1.980s
% 2.21/2.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.21/2.46  % SZS output start Refutation
% 2.21/2.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.21/2.46  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 2.21/2.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.21/2.46  thf(sk_B_type, type, sk_B: $i).
% 2.21/2.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.21/2.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.21/2.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.21/2.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.21/2.46  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.21/2.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.21/2.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.21/2.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.21/2.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.21/2.46  thf(sk_A_type, type, sk_A: $i).
% 2.21/2.46  thf(sk_C_type, type, sk_C: $i).
% 2.21/2.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.21/2.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.21/2.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.21/2.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.21/2.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.21/2.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.21/2.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.21/2.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.21/2.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.21/2.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.21/2.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.21/2.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.21/2.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.21/2.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.21/2.46  thf(fc11_relat_1, axiom,
% 2.21/2.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 2.21/2.46  thf('0', plain,
% 2.21/2.46      (![X6 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 2.21/2.46      inference('cnf', [status(esa)], [fc11_relat_1])).
% 2.21/2.46  thf(t62_tops_2, conjecture,
% 2.21/2.46    (![A:$i]:
% 2.21/2.46     ( ( l1_struct_0 @ A ) =>
% 2.21/2.46       ( ![B:$i]:
% 2.21/2.46         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.21/2.46           ( ![C:$i]:
% 2.21/2.46             ( ( ( v1_funct_1 @ C ) & 
% 2.21/2.46                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.21/2.46                 ( m1_subset_1 @
% 2.21/2.46                   C @ 
% 2.21/2.46                   ( k1_zfmisc_1 @
% 2.21/2.46                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.21/2.46               ( ( ( ( k2_relset_1 @
% 2.21/2.46                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.21/2.46                     ( k2_struct_0 @ B ) ) & 
% 2.21/2.46                   ( v2_funct_1 @ C ) ) =>
% 2.21/2.46                 ( ( ( k1_relset_1 @
% 2.21/2.46                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.21/2.46                       ( k2_tops_2 @
% 2.21/2.46                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.21/2.46                     ( k2_struct_0 @ B ) ) & 
% 2.21/2.46                   ( ( k2_relset_1 @
% 2.21/2.46                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.21/2.46                       ( k2_tops_2 @
% 2.21/2.46                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.21/2.46                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 2.21/2.46  thf(zf_stmt_0, negated_conjecture,
% 2.21/2.46    (~( ![A:$i]:
% 2.21/2.46        ( ( l1_struct_0 @ A ) =>
% 2.21/2.46          ( ![B:$i]:
% 2.21/2.46            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.21/2.46              ( ![C:$i]:
% 2.21/2.46                ( ( ( v1_funct_1 @ C ) & 
% 2.21/2.46                    ( v1_funct_2 @
% 2.21/2.46                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.21/2.46                    ( m1_subset_1 @
% 2.21/2.46                      C @ 
% 2.21/2.46                      ( k1_zfmisc_1 @
% 2.21/2.46                        ( k2_zfmisc_1 @
% 2.21/2.46                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.21/2.46                  ( ( ( ( k2_relset_1 @
% 2.21/2.46                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.21/2.46                        ( k2_struct_0 @ B ) ) & 
% 2.21/2.46                      ( v2_funct_1 @ C ) ) =>
% 2.21/2.46                    ( ( ( k1_relset_1 @
% 2.21/2.46                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.21/2.46                          ( k2_tops_2 @
% 2.21/2.46                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.21/2.46                        ( k2_struct_0 @ B ) ) & 
% 2.21/2.46                      ( ( k2_relset_1 @
% 2.21/2.46                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.21/2.46                          ( k2_tops_2 @
% 2.21/2.46                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.21/2.46                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 2.21/2.46    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 2.21/2.46  thf('1', plain,
% 2.21/2.46      ((m1_subset_1 @ sk_C @ 
% 2.21/2.46        (k1_zfmisc_1 @ 
% 2.21/2.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf(redefinition_k2_relset_1, axiom,
% 2.21/2.46    (![A:$i,B:$i,C:$i]:
% 2.21/2.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.21/2.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.21/2.46  thf('2', plain,
% 2.21/2.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.21/2.46         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.21/2.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.21/2.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.21/2.46  thf('3', plain,
% 2.21/2.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46         = (k2_relat_1 @ sk_C))),
% 2.21/2.46      inference('sup-', [status(thm)], ['1', '2'])).
% 2.21/2.46  thf('4', plain,
% 2.21/2.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46         = (k2_struct_0 @ sk_B))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('5', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.46      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.46  thf(d3_struct_0, axiom,
% 2.21/2.46    (![A:$i]:
% 2.21/2.46     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.21/2.46  thf('6', plain,
% 2.21/2.46      (![X31 : $i]:
% 2.21/2.46         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.46  thf(fc2_struct_0, axiom,
% 2.21/2.46    (![A:$i]:
% 2.21/2.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.21/2.46       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.21/2.46  thf('7', plain,
% 2.21/2.46      (![X32 : $i]:
% 2.21/2.46         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 2.21/2.46          | ~ (l1_struct_0 @ X32)
% 2.21/2.46          | (v2_struct_0 @ X32))),
% 2.21/2.46      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.21/2.46  thf('8', plain,
% 2.21/2.46      (![X0 : $i]:
% 2.21/2.46         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 2.21/2.46          | ~ (l1_struct_0 @ X0)
% 2.21/2.46          | (v2_struct_0 @ X0)
% 2.21/2.46          | ~ (l1_struct_0 @ X0))),
% 2.21/2.46      inference('sup-', [status(thm)], ['6', '7'])).
% 2.21/2.46  thf('9', plain,
% 2.21/2.46      (![X0 : $i]:
% 2.21/2.46         ((v2_struct_0 @ X0)
% 2.21/2.46          | ~ (l1_struct_0 @ X0)
% 2.21/2.46          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 2.21/2.46      inference('simplify', [status(thm)], ['8'])).
% 2.21/2.46  thf('10', plain,
% 2.21/2.46      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.21/2.46        | ~ (l1_struct_0 @ sk_B)
% 2.21/2.46        | (v2_struct_0 @ sk_B))),
% 2.21/2.46      inference('sup-', [status(thm)], ['5', '9'])).
% 2.21/2.46  thf('11', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('12', plain,
% 2.21/2.46      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 2.21/2.46      inference('demod', [status(thm)], ['10', '11'])).
% 2.21/2.46  thf('13', plain, (~ (v2_struct_0 @ sk_B)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('14', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 2.21/2.46      inference('clc', [status(thm)], ['12', '13'])).
% 2.21/2.46  thf('15', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.21/2.46      inference('sup-', [status(thm)], ['0', '14'])).
% 2.21/2.46  thf('16', plain,
% 2.21/2.46      (![X31 : $i]:
% 2.21/2.46         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.46  thf('17', plain,
% 2.21/2.46      (![X31 : $i]:
% 2.21/2.46         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.46  thf('18', plain,
% 2.21/2.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('19', plain,
% 2.21/2.46      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.21/2.46        | ~ (l1_struct_0 @ sk_A))),
% 2.21/2.46      inference('sup+', [status(thm)], ['17', '18'])).
% 2.21/2.46  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('21', plain,
% 2.21/2.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.46      inference('demod', [status(thm)], ['19', '20'])).
% 2.21/2.46  thf('22', plain,
% 2.21/2.46      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.21/2.46        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.46      inference('sup+', [status(thm)], ['16', '21'])).
% 2.21/2.46  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('24', plain,
% 2.21/2.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.21/2.46      inference('demod', [status(thm)], ['22', '23'])).
% 2.21/2.46  thf('25', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.46      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.46  thf('26', plain,
% 2.21/2.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.21/2.46      inference('demod', [status(thm)], ['24', '25'])).
% 2.21/2.46  thf(d1_funct_2, axiom,
% 2.21/2.46    (![A:$i,B:$i,C:$i]:
% 2.21/2.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.21/2.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.21/2.46           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.21/2.46             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.21/2.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.21/2.46           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.21/2.46             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.21/2.46  thf(zf_stmt_1, axiom,
% 2.21/2.46    (![B:$i,A:$i]:
% 2.21/2.46     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.21/2.46       ( zip_tseitin_0 @ B @ A ) ))).
% 2.21/2.46  thf('27', plain,
% 2.21/2.46      (![X18 : $i, X19 : $i]:
% 2.21/2.46         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.21/2.46  thf('28', plain,
% 2.21/2.46      ((m1_subset_1 @ sk_C @ 
% 2.21/2.46        (k1_zfmisc_1 @ 
% 2.21/2.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf(dt_k2_tops_2, axiom,
% 2.21/2.46    (![A:$i,B:$i,C:$i]:
% 2.21/2.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.21/2.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.21/2.46       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 2.21/2.46         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 2.21/2.46         ( m1_subset_1 @
% 2.21/2.46           ( k2_tops_2 @ A @ B @ C ) @ 
% 2.21/2.46           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 2.21/2.46  thf('29', plain,
% 2.21/2.46      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.21/2.46         ((m1_subset_1 @ (k2_tops_2 @ X36 @ X37 @ X38) @ 
% 2.21/2.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 2.21/2.46          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.21/2.46          | ~ (v1_funct_2 @ X38 @ X36 @ X37)
% 2.21/2.46          | ~ (v1_funct_1 @ X38))),
% 2.21/2.46      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 2.21/2.46  thf('30', plain,
% 2.21/2.46      ((~ (v1_funct_1 @ sk_C)
% 2.21/2.46        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.21/2.46        | (m1_subset_1 @ 
% 2.21/2.46           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 2.21/2.46           (k1_zfmisc_1 @ 
% 2.21/2.46            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 2.21/2.46      inference('sup-', [status(thm)], ['28', '29'])).
% 2.21/2.46  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('32', plain,
% 2.21/2.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('33', plain,
% 2.21/2.46      ((m1_subset_1 @ 
% 2.21/2.46        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 2.21/2.46        (k1_zfmisc_1 @ 
% 2.21/2.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 2.21/2.46      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.21/2.46  thf('34', plain,
% 2.21/2.46      (![X31 : $i]:
% 2.21/2.46         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.46  thf('35', plain,
% 2.21/2.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf(zf_stmt_2, axiom,
% 2.21/2.46    (![C:$i,B:$i,A:$i]:
% 2.21/2.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.21/2.46       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.21/2.46  thf('36', plain,
% 2.21/2.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.21/2.46         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 2.21/2.46          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 2.21/2.46          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.21/2.46  thf('37', plain,
% 2.21/2.46      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.21/2.46        | ((u1_struct_0 @ sk_A)
% 2.21/2.46            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 2.21/2.46      inference('sup-', [status(thm)], ['35', '36'])).
% 2.21/2.46  thf('38', plain,
% 2.21/2.46      (![X18 : $i, X19 : $i]:
% 2.21/2.46         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.21/2.46  thf(t113_zfmisc_1, axiom,
% 2.21/2.46    (![A:$i,B:$i]:
% 2.21/2.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.21/2.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.21/2.46  thf('39', plain,
% 2.21/2.46      (![X4 : $i, X5 : $i]:
% 2.21/2.46         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 2.21/2.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.21/2.46  thf('40', plain,
% 2.21/2.46      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.21/2.46      inference('simplify', [status(thm)], ['39'])).
% 2.21/2.46  thf('41', plain,
% 2.21/2.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.21/2.46         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.21/2.46      inference('sup+', [status(thm)], ['38', '40'])).
% 2.21/2.46  thf(t21_relat_1, axiom,
% 2.21/2.46    (![A:$i]:
% 2.21/2.46     ( ( v1_relat_1 @ A ) =>
% 2.21/2.46       ( r1_tarski @
% 2.21/2.46         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.21/2.46  thf('42', plain,
% 2.21/2.46      (![X7 : $i]:
% 2.21/2.46         ((r1_tarski @ X7 @ 
% 2.21/2.46           (k2_zfmisc_1 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 2.21/2.46          | ~ (v1_relat_1 @ X7))),
% 2.21/2.46      inference('cnf', [status(esa)], [t21_relat_1])).
% 2.21/2.46  thf('43', plain,
% 2.21/2.46      (![X0 : $i, X1 : $i]:
% 2.21/2.46         ((r1_tarski @ X0 @ k1_xboole_0)
% 2.21/2.46          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 2.21/2.46          | ~ (v1_relat_1 @ X0))),
% 2.21/2.46      inference('sup+', [status(thm)], ['41', '42'])).
% 2.21/2.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.21/2.46  thf('44', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.21/2.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.21/2.46  thf(t69_xboole_1, axiom,
% 2.21/2.46    (![A:$i,B:$i]:
% 2.21/2.46     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.21/2.46       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 2.21/2.46  thf('45', plain,
% 2.21/2.46      (![X1 : $i, X2 : $i]:
% 2.21/2.46         (~ (r1_xboole_0 @ X1 @ X2)
% 2.21/2.46          | ~ (r1_tarski @ X1 @ X2)
% 2.21/2.46          | (v1_xboole_0 @ X1))),
% 2.21/2.46      inference('cnf', [status(esa)], [t69_xboole_1])).
% 2.21/2.46  thf('46', plain,
% 2.21/2.46      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 2.21/2.46      inference('sup-', [status(thm)], ['44', '45'])).
% 2.21/2.46  thf('47', plain,
% 2.21/2.46      (![X0 : $i, X1 : $i]:
% 2.21/2.46         (~ (v1_relat_1 @ X0)
% 2.21/2.46          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 2.21/2.46          | (v1_xboole_0 @ X0))),
% 2.21/2.46      inference('sup-', [status(thm)], ['43', '46'])).
% 2.21/2.46  thf('48', plain,
% 2.21/2.46      (![X31 : $i]:
% 2.21/2.46         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.46  thf('49', plain,
% 2.21/2.46      ((m1_subset_1 @ sk_C @ 
% 2.21/2.46        (k1_zfmisc_1 @ 
% 2.21/2.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.21/2.46  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.21/2.46  thf(zf_stmt_5, axiom,
% 2.21/2.46    (![A:$i,B:$i,C:$i]:
% 2.21/2.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.21/2.46       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.21/2.46         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.21/2.46           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.21/2.46             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.21/2.46  thf('50', plain,
% 2.21/2.46      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.21/2.46         (~ (zip_tseitin_0 @ X23 @ X24)
% 2.21/2.46          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 2.21/2.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.21/2.46  thf('51', plain,
% 2.21/2.46      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.21/2.46        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.21/2.46      inference('sup-', [status(thm)], ['49', '50'])).
% 2.21/2.46  thf('52', plain,
% 2.21/2.46      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.21/2.46        | ~ (l1_struct_0 @ sk_B)
% 2.21/2.46        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.21/2.46      inference('sup-', [status(thm)], ['48', '51'])).
% 2.21/2.46  thf('53', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.46      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.46  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('55', plain,
% 2.21/2.46      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))
% 2.21/2.46        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.21/2.46      inference('demod', [status(thm)], ['52', '53', '54'])).
% 2.21/2.46  thf('56', plain,
% 2.21/2.46      (((v1_xboole_0 @ sk_C)
% 2.21/2.46        | ~ (v1_relat_1 @ sk_C)
% 2.21/2.46        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.21/2.46      inference('sup-', [status(thm)], ['47', '55'])).
% 2.21/2.46  thf('57', plain,
% 2.21/2.46      ((m1_subset_1 @ sk_C @ 
% 2.21/2.46        (k1_zfmisc_1 @ 
% 2.21/2.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf(cc1_relset_1, axiom,
% 2.21/2.46    (![A:$i,B:$i,C:$i]:
% 2.21/2.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.21/2.46       ( v1_relat_1 @ C ) ))).
% 2.21/2.46  thf('58', plain,
% 2.21/2.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.21/2.46         ((v1_relat_1 @ X9)
% 2.21/2.46          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.21/2.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.21/2.46  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.46      inference('sup-', [status(thm)], ['57', '58'])).
% 2.21/2.46  thf('60', plain,
% 2.21/2.46      (((v1_xboole_0 @ sk_C)
% 2.21/2.46        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.21/2.46      inference('demod', [status(thm)], ['56', '59'])).
% 2.21/2.46  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.21/2.46      inference('sup-', [status(thm)], ['0', '14'])).
% 2.21/2.46  thf('62', plain,
% 2.21/2.46      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.21/2.46      inference('clc', [status(thm)], ['60', '61'])).
% 2.21/2.46  thf('63', plain,
% 2.21/2.46      (((u1_struct_0 @ sk_A)
% 2.21/2.46         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.21/2.46      inference('demod', [status(thm)], ['37', '62'])).
% 2.21/2.46  thf('64', plain,
% 2.21/2.46      ((((u1_struct_0 @ sk_A)
% 2.21/2.46          = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.46        | ~ (l1_struct_0 @ sk_A))),
% 2.21/2.46      inference('sup+', [status(thm)], ['34', '63'])).
% 2.21/2.46  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('66', plain,
% 2.21/2.46      (((u1_struct_0 @ sk_A)
% 2.21/2.46         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.21/2.46      inference('demod', [status(thm)], ['64', '65'])).
% 2.21/2.46  thf('67', plain,
% 2.21/2.46      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.46      inference('demod', [status(thm)], ['19', '20'])).
% 2.21/2.46  thf('68', plain,
% 2.21/2.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.21/2.46         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 2.21/2.46          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 2.21/2.46          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.21/2.46  thf('69', plain,
% 2.21/2.46      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 2.21/2.46        | ((k2_struct_0 @ sk_A)
% 2.21/2.46            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 2.21/2.46      inference('sup-', [status(thm)], ['67', '68'])).
% 2.21/2.46  thf('70', plain,
% 2.21/2.46      (![X31 : $i]:
% 2.21/2.46         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.46  thf('71', plain,
% 2.21/2.46      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.21/2.46      inference('clc', [status(thm)], ['60', '61'])).
% 2.21/2.46  thf('72', plain,
% 2.21/2.46      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 2.21/2.46        | ~ (l1_struct_0 @ sk_A))),
% 2.21/2.46      inference('sup+', [status(thm)], ['70', '71'])).
% 2.21/2.46  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('74', plain,
% 2.21/2.46      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 2.21/2.46      inference('demod', [status(thm)], ['72', '73'])).
% 2.21/2.46  thf('75', plain,
% 2.21/2.46      (((k2_struct_0 @ sk_A)
% 2.21/2.46         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 2.21/2.46      inference('demod', [status(thm)], ['69', '74'])).
% 2.21/2.46  thf('76', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 2.21/2.46      inference('sup+', [status(thm)], ['66', '75'])).
% 2.21/2.46  thf('77', plain,
% 2.21/2.46      (![X31 : $i]:
% 2.21/2.46         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.46  thf('78', plain,
% 2.21/2.46      ((m1_subset_1 @ sk_C @ 
% 2.21/2.46        (k1_zfmisc_1 @ 
% 2.21/2.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf(d4_tops_2, axiom,
% 2.21/2.46    (![A:$i,B:$i,C:$i]:
% 2.21/2.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.21/2.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.21/2.46       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.21/2.46         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 2.21/2.46  thf('79', plain,
% 2.21/2.46      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.21/2.46         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 2.21/2.46          | ~ (v2_funct_1 @ X35)
% 2.21/2.46          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 2.21/2.46          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 2.21/2.46          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 2.21/2.46          | ~ (v1_funct_1 @ X35))),
% 2.21/2.46      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.21/2.46  thf('80', plain,
% 2.21/2.46      ((~ (v1_funct_1 @ sk_C)
% 2.21/2.46        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.21/2.46        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46            = (k2_funct_1 @ sk_C))
% 2.21/2.46        | ~ (v2_funct_1 @ sk_C)
% 2.21/2.46        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46            != (u1_struct_0 @ sk_B)))),
% 2.21/2.46      inference('sup-', [status(thm)], ['78', '79'])).
% 2.21/2.46  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('82', plain,
% 2.21/2.46      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('84', plain,
% 2.21/2.46      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46         = (k2_relat_1 @ sk_C))),
% 2.21/2.46      inference('sup-', [status(thm)], ['1', '2'])).
% 2.21/2.46  thf('85', plain,
% 2.21/2.46      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46          = (k2_funct_1 @ sk_C))
% 2.21/2.46        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 2.21/2.46      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 2.21/2.46  thf('86', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 2.21/2.46      inference('sup+', [status(thm)], ['66', '75'])).
% 2.21/2.46  thf('87', plain,
% 2.21/2.46      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46          = (k2_funct_1 @ sk_C))
% 2.21/2.46        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 2.21/2.46      inference('demod', [status(thm)], ['85', '86'])).
% 2.21/2.46  thf('88', plain,
% 2.21/2.46      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 2.21/2.46        | ~ (l1_struct_0 @ sk_B)
% 2.21/2.46        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46            = (k2_funct_1 @ sk_C)))),
% 2.21/2.46      inference('sup-', [status(thm)], ['77', '87'])).
% 2.21/2.46  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.46      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.46  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.46  thf('91', plain,
% 2.21/2.46      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 2.21/2.46        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46            = (k2_funct_1 @ sk_C)))),
% 2.21/2.46      inference('demod', [status(thm)], ['88', '89', '90'])).
% 2.21/2.46  thf('92', plain,
% 2.21/2.46      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.46         = (k2_funct_1 @ sk_C))),
% 2.21/2.46      inference('simplify', [status(thm)], ['91'])).
% 2.21/2.46  thf('93', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 2.21/2.46      inference('sup+', [status(thm)], ['66', '75'])).
% 2.21/2.46  thf('94', plain,
% 2.21/2.46      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.46        (k1_zfmisc_1 @ 
% 2.21/2.46         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 2.21/2.46      inference('demod', [status(thm)], ['33', '76', '92', '93'])).
% 2.21/2.46  thf('95', plain,
% 2.21/2.46      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.21/2.46         (~ (zip_tseitin_0 @ X23 @ X24)
% 2.21/2.46          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 2.21/2.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 2.21/2.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.21/2.46  thf('96', plain,
% 2.21/2.47      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47         (u1_struct_0 @ sk_B))
% 2.21/2.47        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['94', '95'])).
% 2.21/2.47  thf('97', plain,
% 2.21/2.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 2.21/2.47        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47           (u1_struct_0 @ sk_B)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['27', '96'])).
% 2.21/2.47  thf('98', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('99', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('100', plain,
% 2.21/2.47      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.21/2.47         ((v1_funct_2 @ (k2_tops_2 @ X36 @ X37 @ X38) @ X37 @ X36)
% 2.21/2.47          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.21/2.47          | ~ (v1_funct_2 @ X38 @ X36 @ X37)
% 2.21/2.47          | ~ (v1_funct_1 @ X38))),
% 2.21/2.47      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 2.21/2.47  thf('101', plain,
% 2.21/2.47      ((~ (v1_funct_1 @ sk_C)
% 2.21/2.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 2.21/2.47        | (v1_funct_2 @ 
% 2.21/2.47           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 2.21/2.47           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['99', '100'])).
% 2.21/2.47  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('103', plain,
% 2.21/2.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('104', plain,
% 2.21/2.47      ((v1_funct_2 @ 
% 2.21/2.47        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 2.21/2.47        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 2.21/2.47      inference('demod', [status(thm)], ['101', '102', '103'])).
% 2.21/2.47  thf('105', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 2.21/2.47      inference('sup+', [status(thm)], ['66', '75'])).
% 2.21/2.47  thf('106', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 2.21/2.47      inference('sup+', [status(thm)], ['66', '75'])).
% 2.21/2.47  thf('107', plain,
% 2.21/2.47      ((v1_funct_2 @ 
% 2.21/2.47        (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 2.21/2.47        (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 2.21/2.47      inference('demod', [status(thm)], ['104', '105', '106'])).
% 2.21/2.47  thf('108', plain,
% 2.21/2.47      (((v1_funct_2 @ 
% 2.21/2.47         (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 2.21/2.47         (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['98', '107'])).
% 2.21/2.47  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('110', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('111', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('112', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('113', plain,
% 2.21/2.47      (((m1_subset_1 @ sk_C @ 
% 2.21/2.47         (k1_zfmisc_1 @ 
% 2.21/2.47          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_A))),
% 2.21/2.47      inference('sup+', [status(thm)], ['111', '112'])).
% 2.21/2.47  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('115', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.47      inference('demod', [status(thm)], ['113', '114'])).
% 2.21/2.47  thf('116', plain,
% 2.21/2.47      (((m1_subset_1 @ sk_C @ 
% 2.21/2.47         (k1_zfmisc_1 @ 
% 2.21/2.47          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['110', '115'])).
% 2.21/2.47  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('118', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.21/2.47      inference('demod', [status(thm)], ['116', '117'])).
% 2.21/2.47  thf('119', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('120', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.21/2.47      inference('demod', [status(thm)], ['118', '119'])).
% 2.21/2.47  thf('121', plain,
% 2.21/2.47      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.21/2.47         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 2.21/2.47          | ~ (v2_funct_1 @ X35)
% 2.21/2.47          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 2.21/2.47          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 2.21/2.47          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 2.21/2.47          | ~ (v1_funct_1 @ X35))),
% 2.21/2.47      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.21/2.47  thf('122', plain,
% 2.21/2.47      ((~ (v1_funct_1 @ sk_C)
% 2.21/2.47        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 2.21/2.47        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47            = (k2_funct_1 @ sk_C))
% 2.21/2.47        | ~ (v2_funct_1 @ sk_C)
% 2.21/2.47        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47            != (k2_relat_1 @ sk_C)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['120', '121'])).
% 2.21/2.47  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('124', plain,
% 2.21/2.47      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['24', '25'])).
% 2.21/2.47  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('126', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('127', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('128', plain,
% 2.21/2.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.47         = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('129', plain,
% 2.21/2.47      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.47          = (k2_struct_0 @ sk_B))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_A))),
% 2.21/2.47      inference('sup+', [status(thm)], ['127', '128'])).
% 2.21/2.47  thf('130', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('131', plain,
% 2.21/2.47      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.47         = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('demod', [status(thm)], ['129', '130'])).
% 2.21/2.47  thf('132', plain,
% 2.21/2.47      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.21/2.47          = (k2_struct_0 @ sk_B))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['126', '131'])).
% 2.21/2.47  thf('133', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('134', plain,
% 2.21/2.47      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.21/2.47         = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('demod', [status(thm)], ['132', '133'])).
% 2.21/2.47  thf('135', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('136', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('137', plain,
% 2.21/2.47      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47         = (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['134', '135', '136'])).
% 2.21/2.47  thf('138', plain,
% 2.21/2.47      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47          = (k2_funct_1 @ sk_C))
% 2.21/2.47        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.21/2.47      inference('demod', [status(thm)], ['122', '123', '124', '125', '137'])).
% 2.21/2.47  thf('139', plain,
% 2.21/2.47      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47         = (k2_funct_1 @ sk_C))),
% 2.21/2.47      inference('simplify', [status(thm)], ['138'])).
% 2.21/2.47  thf('140', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('141', plain,
% 2.21/2.47      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 2.21/2.47        (k2_struct_0 @ sk_A))),
% 2.21/2.47      inference('demod', [status(thm)], ['108', '109', '139', '140'])).
% 2.21/2.47  thf('142', plain,
% 2.21/2.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.21/2.47         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 2.21/2.47          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 2.21/2.47          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.21/2.47  thf('143', plain,
% 2.21/2.47      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47           (u1_struct_0 @ sk_B))
% 2.21/2.47        | ((u1_struct_0 @ sk_B)
% 2.21/2.47            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47               (k2_funct_1 @ sk_C))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['141', '142'])).
% 2.21/2.47  thf('144', plain,
% 2.21/2.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 2.21/2.47        | ((u1_struct_0 @ sk_B)
% 2.21/2.47            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47               (k2_funct_1 @ sk_C))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['97', '143'])).
% 2.21/2.47  thf('145', plain,
% 2.21/2.47      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47          != (k2_struct_0 @ sk_B))
% 2.21/2.47        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47            != (k2_struct_0 @ sk_A)))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('146', plain,
% 2.21/2.47      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47          != (k2_struct_0 @ sk_B)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_B))))),
% 2.21/2.47      inference('split', [status(esa)], ['145'])).
% 2.21/2.47  thf('147', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 2.21/2.47      inference('sup+', [status(thm)], ['66', '75'])).
% 2.21/2.47  thf('148', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 2.21/2.47      inference('sup+', [status(thm)], ['66', '75'])).
% 2.21/2.47  thf('149', plain,
% 2.21/2.47      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.47         = (k2_funct_1 @ sk_C))),
% 2.21/2.47      inference('simplify', [status(thm)], ['91'])).
% 2.21/2.47  thf('150', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('151', plain,
% 2.21/2.47      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_B))))),
% 2.21/2.47      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 2.21/2.47  thf('152', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('153', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.47      inference('demod', [status(thm)], ['113', '114'])).
% 2.21/2.47  thf(t132_funct_2, axiom,
% 2.21/2.47    (![A:$i,B:$i,C:$i]:
% 2.21/2.47     ( ( ( v1_funct_1 @ C ) & 
% 2.21/2.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.21/2.47       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.21/2.47           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.21/2.47         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.21/2.47           ( v1_partfun1 @ C @ A ) ) ) ))).
% 2.21/2.47  thf('154', plain,
% 2.21/2.47      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.21/2.47         (((X28) = (k1_xboole_0))
% 2.21/2.47          | ~ (v1_funct_1 @ X29)
% 2.21/2.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 2.21/2.47          | (v1_partfun1 @ X29 @ X30)
% 2.21/2.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 2.21/2.47          | ~ (v1_funct_2 @ X29 @ X30 @ X28)
% 2.21/2.47          | ~ (v1_funct_1 @ X29))),
% 2.21/2.47      inference('cnf', [status(esa)], [t132_funct_2])).
% 2.21/2.47  thf('155', plain,
% 2.21/2.47      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.21/2.47         (~ (v1_funct_2 @ X29 @ X30 @ X28)
% 2.21/2.47          | (v1_partfun1 @ X29 @ X30)
% 2.21/2.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 2.21/2.47          | ~ (v1_funct_1 @ X29)
% 2.21/2.47          | ((X28) = (k1_xboole_0)))),
% 2.21/2.47      inference('simplify', [status(thm)], ['154'])).
% 2.21/2.47  thf('156', plain,
% 2.21/2.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.21/2.47        | ~ (v1_funct_1 @ sk_C)
% 2.21/2.47        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 2.21/2.47        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['153', '155'])).
% 2.21/2.47  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('158', plain,
% 2.21/2.47      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.47      inference('demod', [status(thm)], ['19', '20'])).
% 2.21/2.47  thf('159', plain,
% 2.21/2.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.21/2.47        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 2.21/2.47      inference('demod', [status(thm)], ['156', '157', '158'])).
% 2.21/2.47  thf(d4_partfun1, axiom,
% 2.21/2.47    (![A:$i,B:$i]:
% 2.21/2.47     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.21/2.47       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 2.21/2.47  thf('160', plain,
% 2.21/2.47      (![X26 : $i, X27 : $i]:
% 2.21/2.47         (~ (v1_partfun1 @ X27 @ X26)
% 2.21/2.47          | ((k1_relat_1 @ X27) = (X26))
% 2.21/2.47          | ~ (v4_relat_1 @ X27 @ X26)
% 2.21/2.47          | ~ (v1_relat_1 @ X27))),
% 2.21/2.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.21/2.47  thf('161', plain,
% 2.21/2.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.21/2.47        | ~ (v1_relat_1 @ sk_C)
% 2.21/2.47        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 2.21/2.47        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['159', '160'])).
% 2.21/2.47  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.47      inference('sup-', [status(thm)], ['57', '58'])).
% 2.21/2.47  thf('163', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.47      inference('demod', [status(thm)], ['113', '114'])).
% 2.21/2.47  thf(cc2_relset_1, axiom,
% 2.21/2.47    (![A:$i,B:$i,C:$i]:
% 2.21/2.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.21/2.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.21/2.47  thf('164', plain,
% 2.21/2.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.21/2.47         ((v4_relat_1 @ X12 @ X13)
% 2.21/2.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.21/2.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.21/2.47  thf('165', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 2.21/2.47      inference('sup-', [status(thm)], ['163', '164'])).
% 2.21/2.47  thf('166', plain,
% 2.21/2.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 2.21/2.47        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 2.21/2.47      inference('demod', [status(thm)], ['161', '162', '165'])).
% 2.21/2.47  thf('167', plain,
% 2.21/2.47      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_B)
% 2.21/2.47        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 2.21/2.47      inference('sup+', [status(thm)], ['152', '166'])).
% 2.21/2.47  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('170', plain,
% 2.21/2.47      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 2.21/2.47        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 2.21/2.47      inference('demod', [status(thm)], ['167', '168', '169'])).
% 2.21/2.47  thf(t55_funct_1, axiom,
% 2.21/2.47    (![A:$i]:
% 2.21/2.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.21/2.47       ( ( v2_funct_1 @ A ) =>
% 2.21/2.47         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.21/2.47           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.21/2.47  thf('171', plain,
% 2.21/2.47      (![X8 : $i]:
% 2.21/2.47         (~ (v2_funct_1 @ X8)
% 2.21/2.47          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 2.21/2.47          | ~ (v1_funct_1 @ X8)
% 2.21/2.47          | ~ (v1_relat_1 @ X8))),
% 2.21/2.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.21/2.47  thf('172', plain,
% 2.21/2.47      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('demod', [status(thm)], ['33', '76', '92', '93'])).
% 2.21/2.47  thf('173', plain,
% 2.21/2.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.21/2.47         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.21/2.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.21/2.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.21/2.47  thf('174', plain,
% 2.21/2.47      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['172', '173'])).
% 2.21/2.47  thf('175', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('176', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('177', plain,
% 2.21/2.47      (((m1_subset_1 @ sk_C @ 
% 2.21/2.47         (k1_zfmisc_1 @ 
% 2.21/2.47          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['175', '176'])).
% 2.21/2.47  thf('178', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('179', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 2.21/2.47      inference('demod', [status(thm)], ['177', '178'])).
% 2.21/2.47  thf('180', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('181', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.21/2.47      inference('demod', [status(thm)], ['179', '180'])).
% 2.21/2.47  thf('182', plain,
% 2.21/2.47      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.21/2.47         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 2.21/2.47          | ~ (v2_funct_1 @ X35)
% 2.21/2.47          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 2.21/2.47          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 2.21/2.47          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 2.21/2.47          | ~ (v1_funct_1 @ X35))),
% 2.21/2.47      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.21/2.47  thf('183', plain,
% 2.21/2.47      ((~ (v1_funct_1 @ sk_C)
% 2.21/2.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 2.21/2.47        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47            = (k2_funct_1 @ sk_C))
% 2.21/2.47        | ~ (v2_funct_1 @ sk_C)
% 2.21/2.47        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47            != (k2_relat_1 @ sk_C)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['181', '182'])).
% 2.21/2.47  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('185', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('186', plain,
% 2.21/2.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('187', plain,
% 2.21/2.47      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['185', '186'])).
% 2.21/2.47  thf('188', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('189', plain,
% 2.21/2.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('demod', [status(thm)], ['187', '188'])).
% 2.21/2.47  thf('190', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('191', plain,
% 2.21/2.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['189', '190'])).
% 2.21/2.47  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('193', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('194', plain,
% 2.21/2.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 2.21/2.47         = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('195', plain,
% 2.21/2.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.21/2.47          = (k2_struct_0 @ sk_B))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['193', '194'])).
% 2.21/2.47  thf('196', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('197', plain,
% 2.21/2.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 2.21/2.47         = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('demod', [status(thm)], ['195', '196'])).
% 2.21/2.47  thf('198', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('199', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('200', plain,
% 2.21/2.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47         = (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['197', '198', '199'])).
% 2.21/2.47  thf('201', plain,
% 2.21/2.47      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47          = (k2_funct_1 @ sk_C))
% 2.21/2.47        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 2.21/2.47      inference('demod', [status(thm)], ['183', '184', '191', '192', '200'])).
% 2.21/2.47  thf('202', plain,
% 2.21/2.47      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47         = (k2_funct_1 @ sk_C))),
% 2.21/2.47      inference('simplify', [status(thm)], ['201'])).
% 2.21/2.47  thf('203', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('204', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('205', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('206', plain,
% 2.21/2.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47          != (k2_struct_0 @ sk_A)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('split', [status(esa)], ['145'])).
% 2.21/2.47  thf('207', plain,
% 2.21/2.47      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47           != (k2_struct_0 @ sk_A))
% 2.21/2.47         | ~ (l1_struct_0 @ sk_A)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['205', '206'])).
% 2.21/2.47  thf('208', plain, ((l1_struct_0 @ sk_A)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('209', plain,
% 2.21/2.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47          != (k2_struct_0 @ sk_A)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('demod', [status(thm)], ['207', '208'])).
% 2.21/2.47  thf('210', plain,
% 2.21/2.47      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47           != (k2_struct_0 @ sk_A))
% 2.21/2.47         | ~ (l1_struct_0 @ sk_B)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['204', '209'])).
% 2.21/2.47  thf('211', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('212', plain,
% 2.21/2.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47          != (k2_struct_0 @ sk_A)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('demod', [status(thm)], ['210', '211'])).
% 2.21/2.47  thf('213', plain,
% 2.21/2.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 2.21/2.47          != (k2_struct_0 @ sk_A)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['203', '212'])).
% 2.21/2.47  thf('214', plain,
% 2.21/2.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['202', '213'])).
% 2.21/2.47  thf('215', plain,
% 2.21/2.47      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['174', '214'])).
% 2.21/2.47  thf('216', plain,
% 2.21/2.47      (((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 2.21/2.47         | ~ (v1_relat_1 @ sk_C)
% 2.21/2.47         | ~ (v1_funct_1 @ sk_C)
% 2.21/2.47         | ~ (v2_funct_1 @ sk_C)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['171', '215'])).
% 2.21/2.47  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.47      inference('sup-', [status(thm)], ['57', '58'])).
% 2.21/2.47  thf('218', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('219', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('220', plain,
% 2.21/2.47      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('demod', [status(thm)], ['216', '217', '218', '219'])).
% 2.21/2.47  thf('221', plain,
% 2.21/2.47      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 2.21/2.47         | ((k2_relat_1 @ sk_C) = (k1_xboole_0))))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['170', '220'])).
% 2.21/2.47  thf('222', plain,
% 2.21/2.47      ((((k2_relat_1 @ sk_C) = (k1_xboole_0)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('simplify', [status(thm)], ['221'])).
% 2.21/2.47  thf('223', plain,
% 2.21/2.47      (![X7 : $i]:
% 2.21/2.47         ((r1_tarski @ X7 @ 
% 2.21/2.47           (k2_zfmisc_1 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 2.21/2.47          | ~ (v1_relat_1 @ X7))),
% 2.21/2.47      inference('cnf', [status(esa)], [t21_relat_1])).
% 2.21/2.47  thf('224', plain,
% 2.21/2.47      ((((r1_tarski @ sk_C @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 2.21/2.47         | ~ (v1_relat_1 @ sk_C)))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('sup+', [status(thm)], ['222', '223'])).
% 2.21/2.47  thf('225', plain,
% 2.21/2.47      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.21/2.47      inference('simplify', [status(thm)], ['39'])).
% 2.21/2.47  thf('226', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.47      inference('sup-', [status(thm)], ['57', '58'])).
% 2.21/2.47  thf('227', plain,
% 2.21/2.47      (((r1_tarski @ sk_C @ k1_xboole_0))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('demod', [status(thm)], ['224', '225', '226'])).
% 2.21/2.47  thf('228', plain,
% 2.21/2.47      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 2.21/2.47      inference('sup-', [status(thm)], ['44', '45'])).
% 2.21/2.47  thf('229', plain,
% 2.21/2.47      (((v1_xboole_0 @ sk_C))
% 2.21/2.47         <= (~
% 2.21/2.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47                = (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('sup-', [status(thm)], ['227', '228'])).
% 2.21/2.47  thf('230', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.21/2.47      inference('sup-', [status(thm)], ['0', '14'])).
% 2.21/2.47  thf('231', plain,
% 2.21/2.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47          = (k2_struct_0 @ sk_A)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['229', '230'])).
% 2.21/2.47  thf('232', plain,
% 2.21/2.47      (~
% 2.21/2.47       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47          = (k2_struct_0 @ sk_B))) | 
% 2.21/2.47       ~
% 2.21/2.47       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47          = (k2_struct_0 @ sk_A)))),
% 2.21/2.47      inference('split', [status(esa)], ['145'])).
% 2.21/2.47  thf('233', plain,
% 2.21/2.47      (~
% 2.21/2.47       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 2.21/2.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 2.21/2.47          = (k2_struct_0 @ sk_B)))),
% 2.21/2.47      inference('sat_resolution*', [status(thm)], ['231', '232'])).
% 2.21/2.47  thf('234', plain,
% 2.21/2.47      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 2.21/2.47         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('simpl_trail', [status(thm)], ['151', '233'])).
% 2.21/2.47  thf('235', plain,
% 2.21/2.47      ((((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 2.21/2.47        | ((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['144', '234'])).
% 2.21/2.47  thf('236', plain,
% 2.21/2.47      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('demod', [status(thm)], ['33', '76', '92', '93'])).
% 2.21/2.47  thf('237', plain,
% 2.21/2.47      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.21/2.47         (~ (v1_funct_2 @ X29 @ X30 @ X28)
% 2.21/2.47          | (v1_partfun1 @ X29 @ X30)
% 2.21/2.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 2.21/2.47          | ~ (v1_funct_1 @ X29)
% 2.21/2.47          | ((X28) = (k1_xboole_0)))),
% 2.21/2.47      inference('simplify', [status(thm)], ['154'])).
% 2.21/2.47  thf('238', plain,
% 2.21/2.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 2.21/2.47        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.21/2.47        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 2.21/2.47        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 2.21/2.47             (k2_struct_0 @ sk_A)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['236', '237'])).
% 2.21/2.47  thf('239', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 2.21/2.47      inference('demod', [status(thm)], ['179', '180'])).
% 2.21/2.47  thf('240', plain,
% 2.21/2.47      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.21/2.47         ((v1_funct_1 @ (k2_tops_2 @ X36 @ X37 @ X38))
% 2.21/2.47          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.21/2.47          | ~ (v1_funct_2 @ X38 @ X36 @ X37)
% 2.21/2.47          | ~ (v1_funct_1 @ X38))),
% 2.21/2.47      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 2.21/2.47  thf('241', plain,
% 2.21/2.47      ((~ (v1_funct_1 @ sk_C)
% 2.21/2.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 2.21/2.47        | (v1_funct_1 @ 
% 2.21/2.47           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['239', '240'])).
% 2.21/2.47  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('243', plain,
% 2.21/2.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['189', '190'])).
% 2.21/2.47  thf('244', plain,
% 2.21/2.47      ((v1_funct_1 @ 
% 2.21/2.47        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['241', '242', '243'])).
% 2.21/2.47  thf('245', plain,
% 2.21/2.47      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 2.21/2.47         = (k2_funct_1 @ sk_C))),
% 2.21/2.47      inference('simplify', [status(thm)], ['201'])).
% 2.21/2.47  thf('246', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['244', '245'])).
% 2.21/2.47  thf('247', plain,
% 2.21/2.47      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 2.21/2.47        (k2_struct_0 @ sk_A))),
% 2.21/2.47      inference('demod', [status(thm)], ['108', '109', '139', '140'])).
% 2.21/2.47  thf('248', plain,
% 2.21/2.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 2.21/2.47        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 2.21/2.47      inference('demod', [status(thm)], ['238', '246', '247'])).
% 2.21/2.47  thf('249', plain,
% 2.21/2.47      (![X26 : $i, X27 : $i]:
% 2.21/2.47         (~ (v1_partfun1 @ X27 @ X26)
% 2.21/2.47          | ((k1_relat_1 @ X27) = (X26))
% 2.21/2.47          | ~ (v4_relat_1 @ X27 @ X26)
% 2.21/2.47          | ~ (v1_relat_1 @ X27))),
% 2.21/2.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.21/2.47  thf('250', plain,
% 2.21/2.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 2.21/2.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.21/2.47        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 2.21/2.47        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['248', '249'])).
% 2.21/2.47  thf('251', plain,
% 2.21/2.47      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('demod', [status(thm)], ['33', '76', '92', '93'])).
% 2.21/2.47  thf('252', plain,
% 2.21/2.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.21/2.47         ((v1_relat_1 @ X9)
% 2.21/2.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.21/2.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.21/2.47  thf('253', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.21/2.47      inference('sup-', [status(thm)], ['251', '252'])).
% 2.21/2.47  thf('254', plain,
% 2.21/2.47      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 2.21/2.47      inference('demod', [status(thm)], ['33', '76', '92', '93'])).
% 2.21/2.47  thf('255', plain,
% 2.21/2.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.21/2.47         ((v4_relat_1 @ X12 @ X13)
% 2.21/2.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.21/2.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.21/2.47  thf('256', plain,
% 2.21/2.47      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup-', [status(thm)], ['254', '255'])).
% 2.21/2.47  thf('257', plain,
% 2.21/2.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 2.21/2.47        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B)))),
% 2.21/2.47      inference('demod', [status(thm)], ['250', '253', '256'])).
% 2.21/2.47  thf('258', plain,
% 2.21/2.47      (![X8 : $i]:
% 2.21/2.47         (~ (v2_funct_1 @ X8)
% 2.21/2.47          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 2.21/2.47          | ~ (v1_funct_1 @ X8)
% 2.21/2.47          | ~ (v1_relat_1 @ X8))),
% 2.21/2.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.21/2.47  thf('259', plain,
% 2.21/2.47      (![X31 : $i]:
% 2.21/2.47         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 2.21/2.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.21/2.47  thf('260', plain,
% 2.21/2.47      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup-', [status(thm)], ['254', '255'])).
% 2.21/2.47  thf('261', plain,
% 2.21/2.47      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 2.21/2.47        | ~ (l1_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['259', '260'])).
% 2.21/2.47  thf('262', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 2.21/2.47      inference('sup+', [status(thm)], ['3', '4'])).
% 2.21/2.47  thf('263', plain, ((l1_struct_0 @ sk_B)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('264', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['261', '262', '263'])).
% 2.21/2.47  thf('265', plain,
% 2.21/2.47      (![X8 : $i]:
% 2.21/2.47         (~ (v2_funct_1 @ X8)
% 2.21/2.47          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 2.21/2.47          | ~ (v1_funct_1 @ X8)
% 2.21/2.47          | ~ (v1_relat_1 @ X8))),
% 2.21/2.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.21/2.47  thf('266', plain,
% 2.21/2.47      (![X26 : $i, X27 : $i]:
% 2.21/2.47         (((k1_relat_1 @ X27) != (X26))
% 2.21/2.47          | (v1_partfun1 @ X27 @ X26)
% 2.21/2.47          | ~ (v4_relat_1 @ X27 @ X26)
% 2.21/2.47          | ~ (v1_relat_1 @ X27))),
% 2.21/2.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.21/2.47  thf('267', plain,
% 2.21/2.47      (![X27 : $i]:
% 2.21/2.47         (~ (v1_relat_1 @ X27)
% 2.21/2.47          | ~ (v4_relat_1 @ X27 @ (k1_relat_1 @ X27))
% 2.21/2.47          | (v1_partfun1 @ X27 @ (k1_relat_1 @ X27)))),
% 2.21/2.47      inference('simplify', [status(thm)], ['266'])).
% 2.21/2.47  thf('268', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.21/2.47          | ~ (v1_relat_1 @ X0)
% 2.21/2.47          | ~ (v1_funct_1 @ X0)
% 2.21/2.47          | ~ (v2_funct_1 @ X0)
% 2.21/2.47          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 2.21/2.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['265', '267'])).
% 2.21/2.47  thf('269', plain,
% 2.21/2.47      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.21/2.47        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 2.21/2.47           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.21/2.47        | ~ (v2_funct_1 @ sk_C)
% 2.21/2.47        | ~ (v1_funct_1 @ sk_C)
% 2.21/2.47        | ~ (v1_relat_1 @ sk_C))),
% 2.21/2.47      inference('sup-', [status(thm)], ['264', '268'])).
% 2.21/2.47  thf('270', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.21/2.47      inference('sup-', [status(thm)], ['251', '252'])).
% 2.21/2.47  thf('271', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('272', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('273', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.47      inference('sup-', [status(thm)], ['57', '58'])).
% 2.21/2.47  thf('274', plain,
% 2.21/2.47      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.21/2.47      inference('demod', [status(thm)], ['269', '270', '271', '272', '273'])).
% 2.21/2.47  thf('275', plain,
% 2.21/2.47      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.21/2.47        | ~ (v1_relat_1 @ sk_C)
% 2.21/2.47        | ~ (v1_funct_1 @ sk_C)
% 2.21/2.47        | ~ (v2_funct_1 @ sk_C))),
% 2.21/2.47      inference('sup+', [status(thm)], ['258', '274'])).
% 2.21/2.47  thf('276', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.47      inference('sup-', [status(thm)], ['57', '58'])).
% 2.21/2.47  thf('277', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('278', plain, ((v2_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('279', plain,
% 2.21/2.47      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['275', '276', '277', '278'])).
% 2.21/2.47  thf('280', plain,
% 2.21/2.47      (![X26 : $i, X27 : $i]:
% 2.21/2.47         (~ (v1_partfun1 @ X27 @ X26)
% 2.21/2.47          | ((k1_relat_1 @ X27) = (X26))
% 2.21/2.47          | ~ (v4_relat_1 @ X27 @ X26)
% 2.21/2.47          | ~ (v1_relat_1 @ X27))),
% 2.21/2.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.21/2.47  thf('281', plain,
% 2.21/2.47      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.21/2.47        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 2.21/2.47        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['279', '280'])).
% 2.21/2.47  thf('282', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.21/2.47      inference('sup-', [status(thm)], ['251', '252'])).
% 2.21/2.47  thf('283', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['261', '262', '263'])).
% 2.21/2.47  thf('284', plain,
% 2.21/2.47      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['281', '282', '283'])).
% 2.21/2.47  thf('285', plain,
% 2.21/2.47      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 2.21/2.47        | ((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 2.21/2.47      inference('demod', [status(thm)], ['257', '284'])).
% 2.21/2.47  thf('286', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 2.21/2.47      inference('clc', [status(thm)], ['235', '285'])).
% 2.21/2.47  thf('287', plain, ((v1_funct_2 @ sk_C @ k1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 2.21/2.47      inference('demod', [status(thm)], ['26', '286'])).
% 2.21/2.47  thf('288', plain,
% 2.21/2.47      ((m1_subset_1 @ sk_C @ 
% 2.21/2.47        (k1_zfmisc_1 @ 
% 2.21/2.47         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 2.21/2.47      inference('demod', [status(thm)], ['113', '114'])).
% 2.21/2.47  thf('289', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 2.21/2.47      inference('clc', [status(thm)], ['235', '285'])).
% 2.21/2.47  thf('290', plain,
% 2.21/2.47      (![X4 : $i, X5 : $i]:
% 2.21/2.47         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 2.21/2.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.21/2.47  thf('291', plain,
% 2.21/2.47      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.21/2.47      inference('simplify', [status(thm)], ['290'])).
% 2.21/2.47  thf('292', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.21/2.47      inference('demod', [status(thm)], ['288', '289', '291'])).
% 2.21/2.47  thf('293', plain,
% 2.21/2.47      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.21/2.47         (((X30) != (k1_xboole_0))
% 2.21/2.47          | ~ (v1_funct_1 @ X29)
% 2.21/2.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 2.21/2.47          | (v1_partfun1 @ X29 @ X30)
% 2.21/2.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 2.21/2.47          | ~ (v1_funct_2 @ X29 @ X30 @ X28)
% 2.21/2.47          | ~ (v1_funct_1 @ X29))),
% 2.21/2.47      inference('cnf', [status(esa)], [t132_funct_2])).
% 2.21/2.47  thf('294', plain,
% 2.21/2.47      (![X28 : $i, X29 : $i]:
% 2.21/2.47         (~ (v1_funct_2 @ X29 @ k1_xboole_0 @ X28)
% 2.21/2.47          | (v1_partfun1 @ X29 @ k1_xboole_0)
% 2.21/2.47          | ~ (m1_subset_1 @ X29 @ 
% 2.21/2.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X28)))
% 2.21/2.47          | ~ (v1_funct_1 @ X29))),
% 2.21/2.47      inference('simplify', [status(thm)], ['293'])).
% 2.21/2.47  thf('295', plain,
% 2.21/2.47      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.21/2.47      inference('simplify', [status(thm)], ['290'])).
% 2.21/2.47  thf('296', plain,
% 2.21/2.47      (![X28 : $i, X29 : $i]:
% 2.21/2.47         (~ (v1_funct_2 @ X29 @ k1_xboole_0 @ X28)
% 2.21/2.47          | (v1_partfun1 @ X29 @ k1_xboole_0)
% 2.21/2.47          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.21/2.47          | ~ (v1_funct_1 @ X29))),
% 2.21/2.47      inference('demod', [status(thm)], ['294', '295'])).
% 2.21/2.47  thf('297', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         (~ (v1_funct_1 @ sk_C)
% 2.21/2.47          | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 2.21/2.47          | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ X0))),
% 2.21/2.47      inference('sup-', [status(thm)], ['292', '296'])).
% 2.21/2.47  thf('298', plain, ((v1_funct_1 @ sk_C)),
% 2.21/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.47  thf('299', plain,
% 2.21/2.47      (![X0 : $i]:
% 2.21/2.47         ((v1_partfun1 @ sk_C @ k1_xboole_0)
% 2.21/2.47          | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ X0))),
% 2.21/2.47      inference('demod', [status(thm)], ['297', '298'])).
% 2.21/2.47  thf('300', plain, ((v1_partfun1 @ sk_C @ k1_xboole_0)),
% 2.21/2.47      inference('sup-', [status(thm)], ['287', '299'])).
% 2.21/2.47  thf('301', plain,
% 2.21/2.47      (![X26 : $i, X27 : $i]:
% 2.21/2.47         (~ (v1_partfun1 @ X27 @ X26)
% 2.21/2.47          | ((k1_relat_1 @ X27) = (X26))
% 2.21/2.47          | ~ (v4_relat_1 @ X27 @ X26)
% 2.21/2.47          | ~ (v1_relat_1 @ X27))),
% 2.21/2.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.21/2.47  thf('302', plain,
% 2.21/2.47      ((~ (v1_relat_1 @ sk_C)
% 2.21/2.47        | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 2.21/2.47        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 2.21/2.47      inference('sup-', [status(thm)], ['300', '301'])).
% 2.21/2.47  thf('303', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.47      inference('sup-', [status(thm)], ['57', '58'])).
% 2.21/2.47  thf('304', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.21/2.47      inference('demod', [status(thm)], ['288', '289', '291'])).
% 2.21/2.47  thf('305', plain,
% 2.21/2.47      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.21/2.47      inference('simplify', [status(thm)], ['39'])).
% 2.21/2.47  thf('306', plain,
% 2.21/2.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.21/2.47         ((v4_relat_1 @ X12 @ X13)
% 2.21/2.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.21/2.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.21/2.47  thf('307', plain,
% 2.21/2.47      (![X0 : $i, X1 : $i]:
% 2.21/2.47         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.21/2.47          | (v4_relat_1 @ X1 @ X0))),
% 2.21/2.47      inference('sup-', [status(thm)], ['305', '306'])).
% 2.21/2.47  thf('308', plain, (![X0 : $i]: (v4_relat_1 @ sk_C @ X0)),
% 2.21/2.47      inference('sup-', [status(thm)], ['304', '307'])).
% 2.21/2.47  thf('309', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 2.21/2.47      inference('demod', [status(thm)], ['302', '303', '308'])).
% 2.21/2.47  thf('310', plain,
% 2.21/2.47      (![X7 : $i]:
% 2.21/2.47         ((r1_tarski @ X7 @ 
% 2.21/2.47           (k2_zfmisc_1 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 2.21/2.47          | ~ (v1_relat_1 @ X7))),
% 2.21/2.47      inference('cnf', [status(esa)], [t21_relat_1])).
% 2.21/2.47  thf('311', plain,
% 2.21/2.47      (((r1_tarski @ sk_C @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_C)))
% 2.21/2.47        | ~ (v1_relat_1 @ sk_C))),
% 2.21/2.47      inference('sup+', [status(thm)], ['309', '310'])).
% 2.21/2.47  thf('312', plain,
% 2.21/2.47      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.21/2.47      inference('simplify', [status(thm)], ['290'])).
% 2.21/2.47  thf('313', plain, ((v1_relat_1 @ sk_C)),
% 2.21/2.47      inference('sup-', [status(thm)], ['57', '58'])).
% 2.21/2.47  thf('314', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 2.21/2.47      inference('demod', [status(thm)], ['311', '312', '313'])).
% 2.21/2.47  thf('315', plain,
% 2.21/2.47      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 2.21/2.47      inference('sup-', [status(thm)], ['44', '45'])).
% 2.21/2.47  thf('316', plain, ((v1_xboole_0 @ sk_C)),
% 2.21/2.47      inference('sup-', [status(thm)], ['314', '315'])).
% 2.21/2.47  thf('317', plain, ($false), inference('demod', [status(thm)], ['15', '316'])).
% 2.21/2.47  
% 2.21/2.47  % SZS output end Refutation
% 2.21/2.47  
% 2.34/2.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
